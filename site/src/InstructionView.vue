<template>
  <div>
    <div class="arch-select">
      <span v-for="group in architectureGroups" :key="group" :class="{
        'arch-group': true,
        'selected': containsArchitecture(group, selectedArch)
      }" @click="switchArch(architectureNames[group[0]])">
        <span :for="'group' + JSON.stringify(group)">
          <span v-for="n in group" :key="n">
            {{ architectureNames[n] }}
          </span>
        </span>
      </span>
    </div>
    <AnalysisResults
      v-if="encoding !== null"
      :info="encoding"
      :instr="instruction"
      v-on:change="instructionChanged"
    />
    <div v-else-if="loading">
      <Loader></Loader>
    </div>
    <div v-else>
      Not found...
    </div>
  </div>
</template>

<script>
import InstructionInput from "./components/InstructionInput.vue";
import AnalysisResults from "./components/AnalysisResults.vue";
import Loader from "./components/Loader.vue";
import { FetchStatusCode } from 'liblisa-wasm';

export default {
  name: "InstructionView",
  components: {
    InstructionInput,
    AnalysisResults,
    Loader,
  },
  data() {
    return {
      instruction: '',
      encoding: null,
      loading: true,
      errorMessage: '',
      architectureGroups: [],
      statusCode: FetchStatusCode.Success,
      selectedArch: '3900X',
    };
  },
  async created() {
    this.StatusSuccess = FetchStatusCode.Success;
    this.StatusOutOfScope = FetchStatusCode.OutOfScope;
    this.MissingOnArchitecture = FetchStatusCode.MissingOnArchitecture;

    await this.$fetcher.load_index();
    this.instruction = this.$route.params.instr.toUpperCase();
    if (this.$route.query.arch) {
      this.selectedArch = this.$route.query.arch;
    }

    let architectureNames = JSON.parse(await this.$fetcher.architectures());
    console.log("Architectures: ", architectureNames);
    this.architectureNames = architectureNames;

    await this.fetchAnalysisResults();

    this.$watch(
      () => this.$route.params.instr,
      async (newInstruction, oldInstr) => {
        this.instruction = newInstruction;
        await this.fetchAnalysisResults();
      }
    );
    this.$watch(
      () => this.$route.query.arch,
      async (newArch, oldArch) => {
        if (newArch) {
          this.selectedArch = newArch;
          await this.fetchAnalysisResults();
        }
      }
    );
  },
  methods: {
    containsArchitecture(groupIndices, name) {
      return groupIndices.some(n => this.architectureNames[n] == name)
    },
    switchArch(arch) {
      console.log('Switching arch:', arch);
      if (this.$route.query.arch != arch) {
        this.$router.push({ name: 'instruction', params: { instr: this.instruction.toUpperCase() }, query: { arch } });
      }
    },
    instructionChanged(newInstruction) {
      this.update(newInstruction, false);
    },
    update(instruction, replace) {
      console.log('Updating instruction:', instruction, 'replace=', replace);
      if (this.$route.params.instr != instruction) {
        let target = { name: 'instruction', params: { instr: instruction.toUpperCase() }, query: { arch: this.$route.query.arch } };
        if (replace) {
          this.$router.replace(target);
        } else {
          this.$router.push(target);
        }
      }
    },
    async fetchAnalysisResults() {
      let instr = this.instruction;

      this.encoding = null;
      this.loading = true;
      this.errorMessage = '';

      // TODO: If we're still searching, block until we can continue

      document.title = instr + ' - libLISA';

      console.log("Fetching:", instr, this.selectedArch);
      let result = await this.$fetcher.get(instr, this.selectedArch);

      let status = result.status();
      this.statusCode = status.code();
      this.architectureGroups = JSON.parse(result.architecture_groups());
      if (status.code() == FetchStatusCode.Success) {
        this.encoding = null;
        this.encoding = result.encoding();

        if (this.encoding.byte_len() * 2 < instr.length) {
          this.update(instr.substring(0, this.encoding.byte_len() * 2));
          return;
        }

        let selectedArchitectures = '';
        for (let group of this.architectureGroups) {
          if (this.containsArchitecture(group, this.selectedArch)) {
            selectedArchitectures = group.map(n => this.architectureNames[n]).join(', ');
          }
        }

        document.title = instr + ' on ' + selectedArchitectures + ' - libLISA';
      } else {
        this.encoding = null;
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
            this.$router.replace({ name: 'search', query: { q: instr } });
            m = "No encodings found";
            break;
          case FetchStatusCode.UnknownError:
            m = "An error without status code occurred";
            break;
          case FetchStatusCode.MissingOnArchitecture:
            m = "This instruction is not available on the selected architecture";
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
.arch-select {
  display: flex;
  justify-content: center;
  align-items: center;
}

.arch-group {
  border-radius: 4px 4px;
  background: #eee;
  border: 1px solid #bbb;
  padding: 4px;
  margin: 4px;
  cursor: pointer;
}

.arch-group:hover {
  background: #aaa;
}

.arch-group.selected {
  background: #1c5dcf;
  color: #fff;
}

.arch-group span + span::before {
  content: " | ";
}
</style>