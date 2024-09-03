<template>
  <span v-if="arg.TinyConst !== undefined || arg.Const !== undefined">
    {{ hexConst }}
  </span>
  <span v-else-if="arg.Input !== undefined">
    {{ encoding }}(<template v-if="input.currentValue !== undefined && input.currentValue !== null && input.currentValue != ''">
      <FilledInSource :value="input.currentValue" :chosen="input.class" :actualSource="input.source" />
    </template>
    <template v-else>
      <Source :source="input.source" :chosen="input.class" />
    </template>)
  </span>
  <span v-else> ERROR: unexpected {{ arg }} </span>
</template>

<script>
import Source from "../Source.vue";
import FilledInSource from "../FilledInSource.vue";

export default {
  name: "Arg",
  components: {
    Source,
    FilledInSource,
  },
  props: {
    arg: Object,
    context: Object,
  },
  computed: {
    hexConst() {
      if (this.arg.TinyConst !== undefined) {
        return "0x" + this.arg.TinyConst.toString(16);
      } else {
        return (
          "0x" + this.context.computation.consts[this.arg.Const].toString(16)
        );
      }
    },
    encoding() {
      const encoding = this.arg.Input.encoding;
      if (encoding == "SignedLittleEndian") {
        return "sle";
      } else if (encoding == "SignedBigEndian") {
        return "sbe";
      } else if (encoding == "UnsignedLittleEndian") {
        return "ule";
      } else if (encoding == "UnsignedBigEndian") {
        return "ube";
      } else {
        return "error" + JSON.stringify(encoding);
      }
    },
    input() {
        // console.log(this.context.inputs[this.arg.Input.index]);
        return this.context.inputs[this.arg.Input.index];
    }
  },
  methods: {},
};
</script>

<style scoped></style>
