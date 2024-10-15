<template>
  <span class="node" @click="selectSelf">
    <Arg
      v-if="node.op.Hole !== undefined"
      :arg="context.computation.arg_interpretation[node.op.Hole]"
      :context="context"
    />
    <span v-else-if="infix"><!--
        --><template v-if="needsParens">(</template><Node :node="node.args[0]" :context="context" :needsParens="true" /><!--
        -->{{ formattedName }}<!--
        --><Node :node="node.args[1]" :context="context" :needsParens="true" /><template v-if="needsParens">)</template><!--
    --></span>
    <span v-else>
      {{ formattedName }}<!--
      --><span v-if="node.args.length > 0"
      ><!--
      -->(<!--
      --><template v-for="(arg, argIndex) in node.args" :key="argIndex"><!--
        --><template v-if="argIndex != 0">,</template><!--
        --><Node :node="arg" :context="context" :needsParens="false" /><!--
      --></template><!--
      -->)<!--
      --></span>
    </span>
  </span>
</template>

<script>
/* eslint-disable vue/no-v-for-template-key: 0 */

import Arg from "./Arg.vue";

const INFIX_NAMES = {
  Add: "+",
  Sub: "-",
  Mul: "*",
  Div: "/",
  UnsignedDiv: "//",
  Rem: "%",
  UnsignedRem: "%%",
  Shl: "<<",
  Shr: ">>",
  And: "&",
  Or: "|",
  Xor: "^",
  CmpLt: "<",
};

export default {
  name: "Node",
  components: {
    Arg,
  },
  props: {
    node: Object,
    context: Object,
    needsParens: Boolean,
  },
  computed: {
    infix() {
      let op = this.node.op;

      if (op in INFIX_NAMES) {
        return true;
      } else {
        return false;
      }
    },
    formattedName() {
      let op = this.node.op;

      if (op.Hole !== undefined) {
        return "<" + op.Hole + ">";
      } else if (op.Const !== undefined) {
        return "0x" + op.Const.toString(16);
      } else if (op in INFIX_NAMES) {
        return INFIX_NAMES[op];
      } else if (op.Crop !== undefined) {
        return "Crop[" + op.Crop.num_bits + "]";
      } else if (op.Select !== undefined) {
        return (
          "Select[" +
          op.Select.num_skip +
          ":" +
          (op.Select.num_skip|0 +
          op.Select.num_take|0) +
          "]"
        );
      } else if (op.SignExtend !== undefined) {
        return "SignExtend[" + op.SignExtend.num_bits + "]";
      } else if (op.SwapBytes !== undefined) {
        return "SwapBytes[" + op.SwapBytes.num_bits + "]";
      } else if (op.SetBit !== undefined) {
        return "SetBit[" + op.SetBit.bit + "]";
      } else if (op.Rol !== undefined) {
        return "Rol[" + op.Rol.num_bits + "]";
      } else {
        return op;
      }
    },
  },
  methods: {
    selectSelf(ev) {
        let target = ev.target;
        while (target && !target.classList.contains("node")) {
            target = target.parentNode;
        }
        console.log(ev, target);
        if (window.getSelection && document.createRange) {
            let selection = window.getSelection();
            let range = document.createRange();
            range.selectNodeContents(target);
            selection.removeAllRanges();
            selection.addRange(range);
        } else if (document.selection && document.body.createTextRange) {
            let range = document.body.createTextRange();
            range.moveToElementText(target);
            range.select();
        }
    }
  },
};
</script>

<style scoped>
.node {
    padding: 4px;
    cursor: default;
}

.node:hover {
    background: rgba(0, 0, 0, 0.05);
}
</style>
