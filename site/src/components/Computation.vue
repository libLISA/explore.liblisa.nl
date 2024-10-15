<template>
  <span>
    <Node :node="computationTree" :context="context" :needsParens="false" />
  </span>
</template>

<script>
import Node from "./ComputationParts/Node.vue";

function numArgs(op) {
  if (op.Hole !== undefined || op.Const !== undefined) {
    return 0;
  } else if (
    op === "Not" ||
    op == "IsZero" ||
    op.Crop !== undefined ||
    op.Select !== undefined ||
    op == "Parity" ||
    op.SignExtend !== undefined ||
    op.SetBit !== undefined ||
    op.SwapBytes !== undefined ||
    op == "ByteMask" ||
    op == "BitMask" ||
    op == "TrailingZeros" ||
    op == "LeadingZeros" ||
    op == "PopCount"
  ) {
    return 1;
  } else if (
    op === "Add" ||
    op === "Sub" ||
    op === "Mul" ||
    op === "CarrylessMul" ||
    op === "Div" ||
    op === "UnsignedDiv" ||
    op === "Rem" ||
    op === "UnsignedRem" ||
    op === "Shl" ||
    op === "Shr" ||
    op === "And" ||
    op === "Or" ||
    op === "Xor" ||
    op === "CmpLt" ||
    op.Rol !== undefined ||
    op === "DepositBits" ||
    op === "ExtractBits"
  ) {
    return 2;
  } else if (op == "IfZero") {
    return 3;
  } else {
    console.log("Unknown operation:" + JSON.stringify(op));
    return 0;
  }
}

export default {
  name: "Computation",
  components: {
    Node,
  },
  props: {
    computation: Object,
    inputs: Object,
  },
  computed: {
    context() {
      return {
        inputs: this.inputs,
        computation: this.computation,
      };
    },
    computationTree() {
      let ops = this.computation.expr.ops;
      let stack = [];

      for (const op of ops) {
        const argCount = numArgs(op);
        let args = [];
        while (args.length < argCount) {
          args.push(stack.pop());
        }

        args.reverse();

        stack.push({
          op,
          args,
        });
      }

      return stack.pop();
    },
  },
  methods: {},
};
</script>

<style scoped></style>
