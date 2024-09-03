<template>
    <ul class="flow-list">
      <li
        v-for="result, resultIndex in searchResults"
        :key="resultIndex"
        @click="openInstr(result.matching_instr, result.architectures)"
      >
        <span class="tt instr-bytes"><strong>{{ result.matching_instr.substring(0, instruction.length) }}</strong>{{ result.matching_instr.substring(instruction.length) }}: </span>
        <span class="tt instr-bits">
          <span v-for="bit, index in result.match_bits" :key="index" :class="{ 
            ['text-chosen' + bit.part_index]: bit.part_index !== null, 
            ['matched']: bit.matched
          }">
            {{ bit.part_index !== null ? ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i'][bit.part_index] : bit.bit_value }}
          </span>
        </span>
        <span class="architectures" v-if="result.architectures.length != architectureNames.length">
          <span v-for="n in result.architectures" :key="n">{{ architectureNames[n] }}</span>
        </span>
      </li>
    </ul>
</template>

<script>
import InstructionInput from "./InstructionInput.vue";
import Loader from "./Loader.vue";
import { FetchStatusCode } from 'liblisa-wasm';

export default {
  name: "Search",
  components: {
    InstructionInput,
    Loader,
  },
  props: {
    instruction: String,
    searchResults: Object,
  },
  data() {
    return {
      timer: null,
      loading: false,
      errorMessage: '',
      statusCode: FetchStatusCode.Success,
      architectureNames: [],
    };
  },
  computed: {},
  async created() {
    this.StatusSuccess = FetchStatusCode.Success;
    this.StatusOutOfScope = FetchStatusCode.OutOfScope;

    await this.$fetcher.load_index();
    let architectureNames = JSON.parse(await this.$fetcher.architectures());
    console.log("Architectures: ", architectureNames);
    this.architectureNames = architectureNames;
  },
  methods: {
    openInstr(instruction, architectures) {
      let arch = this.architectureNames[architectures[0]];
      if (architectures.length != this.architectureNames.length) {
        this.$router.push({ name: 'instruction', params: { instr: instruction }, query: { arch } })
      } else {
        this.$router.push({ name: 'instruction', params: { instr: instruction } })
      }
    },
  },
  emits: ["choose"],
};
</script>

<style scoped>
.flow-list {
  min-width: 30%;
  font-size: 1.5em;
  justify-content: flex-start;
}

.flow-list.loading {
  opacity: .5;
  pointer-events: none;
}

.flow-list li:hover {
  background: #1c5dcf;
  color: #fff;
  cursor: pointer;
}

.instr-bits {
  padding-left: 10pt;
  color: #000;
}

.instr-bits *:nth-child(8n) {
  padding-right: 5pt;
}

.instr-bits *:nth-child(8n+1) {
  padding-left: 5pt;
}

.instr-bits * {
  opacity: 0.7;
  transition: opacity ease 0.5s;
}

.instr-bits .matched {
  opacity: 1;
  background: #ddd;
}

.architectures {
  margin-left: auto;
}

.architectures span {
  border-radius: 4px 4px;
  background: #aaa;
  font-size: .6em;
  padding: 4px;
  margin: 4px;
}
</style>
