<template>
  <div class="main">
    <h1>libLISA - Instruction discovery and analysis on x86-64</h1>
    <InstructionInput
      :placeholder="'Enter an instruction, for example: 0000'"
      v-model="instruction"
    />
    <SearchResults :instruction="instruction" :searchResults="searchResults" />

    <Loader v-if="loading">
    </Loader>

    <div v-if="instruction == ''">
      <p>
        Enter any instruction in hexadecimal format into the input field above to view its semantics.
      </p>

      <p>
        These semantics have been inferred automatically using <i>libLISA</i>.
        libLISA can automatically scan the instruction space of a CPU, discover all instructions, and synthesize semantics for most of these instructions.
        This dataset shows the results of running libLISA on five different x86-64 architectures. 
      </p>

      <p>
        Some examples of instructions are:
        <ul>
          <li><InstructionLink instr="480FBBD8"><span class="tt">BTC RAX, RBX</span></InstructionLink></li>
          <li><InstructionLink instr="00d3"><span class="tt">ADD BL, DL</span></InstructionLink> / <InstructionLink instr="01d3"><span class="tt">ADD EBX, EDX</span></InstructionLink> / <InstructionLink instr="4801d3"><span class="tt">ADD RBX, RDX</span></InstructionLink></li>
          <li><InstructionLink instr="7240"><span class="tt">JB 0x42</span></InstructionLink></li>
          <li><InstructionLink instr="C5F1FDC2"><span class="tt">VPADDW XMM0, XMM1, XMM2</span></InstructionLink></li>
        </ul>
      </p>

      <p>
        The majority of the instructions (around 80%) behave identically on different architectures.
        Some instructions behave differently on different architectures.
        For example, for the <InstructionLink instr="0fafc3"><span class="tt">IMUL</span> instruction</InstructionLink> the <span class="tt">PF</span>, <span class="tt">AF</span> and <span class="tt">ZF</span> flag are computed differently depending on the architecture.
        In such a case, you can select the architecture that you want to view at the top of the page.
      </p>

      <p>
        Some instructions are not available on all architectures.
        For example, the <InstructionLink instr="0F38C9C1"><span class="tt">SHA1MSG1</span> instruction</InstructionLink> is not supported on the Intel Xeon Silver 4110.
        The SHA1 instructions are not supported in the Skylake microarchitecture, which the Intel Xeon Silver 4110 uses.
        When an instruction is not supported on an architecture, the architecture is not listed in the selection at the top of the page.
      </p>

      <p>
        We do not have support for synthesis of floating point operations, but we can analyze these instructions and generate encodings.
        For example, <InstructionLink instr="D8C2">FADD ST,ST(2)</InstructionLink> is missing computations for its outputs.
        This restriction only applies to instructions that perform floating point operations, not to instructions that use floating point registers.
        When an instruction performs integer operations on floating point registers, we can synthesize computations.
        For example: <InstructionLink instr="0FFDC1">PADDW MM0, MM1</InstructionLink>, which uses the MMX registers.
        The MMX registers re-use the ST(N) x87 floating point registers.
      </p>
    </div>
    <div v-else-if="statusCode != StatusSuccess">
      <div v-if="statusCode == StatusOutOfScope">
        <h2>Out of scope</h2>
        <p>
          We restrict the enumeration scope to keep the runtime feasible.
          We exclude instructions with the following prefixes from being analyzed: 
          <span class="tt">REPNZ</span> (<span class="tt">F2</span>), 
          <span class="tt">REPZ</span> (<span class="tt">F3</span>),
          segment overrides (<span class="tt">26</span>, <span class="tt">2E</span>, <span class="tt">36</span>, <span class="tt">3E</span>, <span class="tt">64</span>, <span class="tt">65</span>),
          and data overrides and address size overrides (<span class="tt">66</span>, <span class="tt">67</span>).
        </p>
        <p>
          These prefixes can appear in front of any (non-VEX prefixed) instruction.
          Even when enforcing a prefix order and excluding invalid sequences of prefixes, including these prefixes would increase runtime by a factor of 84x.
          We also exclude instructions that contain a <span class="tt">REX</span> (<span class="tt">40</span>-<span class="tt">4F</span>) prefix before a lock prefix (<span class="tt">F0</span>).
          The <span class="tt">LSS</span> instruction is also excluded from analysis, as analysis is unreliable and slow for this instruction.
        </p>
      </div>
      <div v-else>
        <p>{{ errorMessage }}</p>
      </div>
    </div>
  </div>
</template>

<script>
import InstructionInput from "./components/InstructionInput.vue";
import InstructionLink from "./components/InstructionLink.vue";
import SearchResults from "./components/SearchResults.vue";
import Loader from "./components/Loader.vue";
import { FetchStatusCode } from 'liblisa-wasm';

let requestedSearchId = 0;
let shownSearchId = 0;

let lastRouteChange = 0;

export default {
  name: "SearchView",
  components: {
    InstructionInput,
    InstructionLink,
    SearchResults,
    Loader,
  },
  data() {
    return {
      instruction: '',
      searchResults: [],
      loading: false,
    };
  },
  async created() {
    this.StatusSuccess = FetchStatusCode.Success;
    this.StatusOutOfScope = FetchStatusCode.OutOfScope;

    await this.$fetcher.load_index();
    let architectureNames = JSON.parse(await this.$fetcher.architectures());
    console.log("Architectures: ", architectureNames);
    this.architectureNames = architectureNames;

    if (this.$route.query.q) {
      this.instruction = this.$route.query.q;
    }

    if (this.instruction != '') {
      await this.fetchAnalysisResults();
    }

    this.$watch(
      () => this.$route.query.q,
      async (q, oldTerm) => {
        this.instruction = q;
        await this.fetchAnalysisResults();
      }
    );
  },
  watch: {
    instruction() {
      console.log('instruction changed: ', this.instruction);
      console.log('current route: ', this.$route.name);

      let timeDelta = Date.now() - lastRouteChange;
      lastRouteChange = Date.now();

      console.log('route change delta: ', timeDelta);

      if (this.instruction == '') {
        this.$router.push({ name: 'home' });
      } else if (this.$route.name != 'search' || timeDelta > 10 * 1000) {
        console.log('pushing search route');
        this.$router.push({ name: 'search', query: { q: this.instruction }});
      } else {
        console.log('replacing search route');
        this.$router.replace({ name: 'search', query: { q: this.instruction }});
      }
    },
  },
  methods: {
    analyze() {
      this.fetchAnalysisResults();
    },
    openInstr(instruction, architectures) {
      let arch = this.architectureNames[architectures[0]];
      if (architectures.length != this.architectureNames.length) {
        this.$router.push({ name: 'instruction', params: { instr: instruction }, query: { arch } })
      } else {
        this.$router.push({ name: 'instruction', params: { instr: instruction } })
      }
    },
    async randomInstruction() {
      this.loading = true;
      this.instruction = await findRandom(arch);
      this.loading = false;
    },
    async fetchAnalysisResults() {
      if (this.instruction == undefined) {
        this.instruction = "";
      }

      let instr = this.instruction;

      let id = requestedSearchId++;
      this.loading = true;
      this.errorMessage = '';

      // TODO: If we're still searching, block until we can continue
      if (this.instruction != '') {
        document.title = "Instructions matching " + this.instruction + ' - libLISA';
      } else {
        document.title = "Explore - libLISA";
      }

      let result = await this.$fetcher.search(instr);
      console.log("Result for search ID", id, "with current shown", shownSearchId, "is", result);

      if (shownSearchId > id) {
        console.log("Results from search ID ", id, " superseded by ", shownSearchId);
        return;
      } else {
        shownSearchId = id;
      }

      let status = result.status();
      this.statusCode = status.code();
      if (status.code() == FetchStatusCode.Success) {
        let results = JSON.parse(result.results());
        console.log("Result:", results);
        this.searchResults.splice(0, this.searchResults.length, ...results);
      } else {
        this.searchResults.splice(0);
        let m;

        switch (status.code()) {
          case FetchStatusCode.DataCorrupted:
            m = "Data corrupted";
            break;
          case FetchStatusCode.InvalidHex:
            m = "Instruction contains invalid hexadecimal characters";
            break;
          case FetchStatusCode.NetworkError:
            m = "A network error occurred";
            break;
          case FetchStatusCode.NotFound:
            m = "No encodings found";
            break;
          case FetchStatusCode.UnknownError:
            m = "An error without status code occurred";
            break;
          default:
            m = "Unknown status code: " + status.code();
            break;
        }

        if (status.message() != '') {
          m += ": " + status.message();
        }

        this.errorMessage = m;
      }

      this.loading = false;
    },
  },
};
</script>

<style scoped>
.main {
  display: flex;
  justify-content: center;
  margin: 0px 16px;
  flex-grow: 1;
  flex-direction: column;
  justify-content: flex-start;
  max-width: 1200px;
  margin: auto;
}

p {
  max-width: 800px;
  margin-left: auto;
  margin-right: auto;
  text-align: left;
}

.tt {
  font-family: monospace;
}
</style>