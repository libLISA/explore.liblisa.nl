<template>
  <span class="dest-container">
    <span :class="['dest', 'input-component', chosen]">
      <span v-if="dest.Reg !== undefined">
        <Reg :reg="dest.Reg[0]" :range="dest.Reg[1]" />
      </span>
      <span v-else-if="dest.Mem !== undefined">
        m<sub>{{ dest.Mem[0] }}</sub>
      </span>
      <span v-else-if="dest.Part !== undefined"> Part {{ dest.Part }} </span>
    </span>
    <span v-if="dest.Reg !== undefined" class="bytes copy-sibling-chosen-bg">
      <span class="copy-only">[</span>{{ dest.Reg[1].start_byte }}<template v-if="dest.Reg[1].start_byte != dest.Reg[1].end_byte">:{{ dest.Reg[1].end_byte }}</template><span class="copy-only">]</span>
    </span>
    <span v-if="dest.Mem !== undefined" class="bytes">
      <span class="copy-only">[</span>{{ dest.Mem[1].start_byte }}<template v-if="dest.Mem[1].start_byte != dest.Mem[1].end_byte">:{{ dest.Mem[1].end_byte }}</template><span class="copy-only">]</span>
    </span>
  </span>
</template>

<script>
import Reg from "./Reg.vue";

export default {
  name: "Dest",
  components: {
    Reg,
  },
  props: {
    dest: Object,
    chosen: String,
  },
  computed: {},
  methods: {},
};
</script>

<style scoped>
.dest-container {
  display: inline-flex;
  position: relative;
}

.copy-only {
  color: rgba(0, 0, 0, 0);
  width: 0;
  overflow: hidden;
  margin: 0;
  padding: 0;
  display: inline-block;
  height: 1px;
}

.bytes {
  position: relative;
  left: -10px;
  top: .7em;
  background: #eee;
  padding: 3px;
  border-radius: 5px;
  box-shadow: rgba(0, 0, 0, .3) 1px 1px 2px;
  align-self: flex-end;
  font-family: monospace;
  font-weight: 900;
}
</style>
