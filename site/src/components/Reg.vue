<template>
  <span v-if="reg === null || reg === undefined"> NULL </span>
  <span v-else-if="specialRegisterName !== null">
    <span class="reg">
      {{ specialRegisterName }}
    </span>
  </span>
  <span class="reg" v-else>
    <span v-if="reg.GpReg !== undefined" class="reg">
      {{ reg.GpReg }}
    </span>
    <span v-else-if="reg.Xmm !== undefined && reg.Xmm.Reg !== undefined" class="reg">
      Xmm{{ reg.Xmm.Reg }}
    </span>
    <span v-else-if="reg.X87 !== undefined && reg.X87.Fpr !== undefined" class="reg">
      mm{{ reg.X87.Fpr }}
    </span>
    <span v-else class="reg">
      {{ JSON.stringify(reg) }}
    </span>
    <!-- TODO: Other X87 registers, Xmm flags -->
  </span>
</template>

<script>
function specialNameFrom(base, r) {
  if (r === undefined) {
    return null;
  }

  if (r.start_byte == 0 && r.end_byte == 0) {
    return base + "L";
  } else if (r.start_byte == 0 && r.end_byte == 1) {
    return base + "X";
  } else if (r.start_byte == 1 && r.end_byte == 1) {
    return base + "H";
  } else if (r.start_byte == 0 && r.end_byte == 3) {
    return "E" + base + "X";
  } else {
    return null;
  }
}

export default {
  name: "Reg",
  props: {
    reg: Object,
    range: Object,
  },
  computed: {
    specialRegisterName() {
      if (this.reg !== null && this.reg.GpReg !== undefined) {
        if (["Rax", "Rbx", "Rcx", "Rdx"].includes(this.reg.GpReg)) {
          return specialNameFrom(
            this.reg.GpReg.substring(1, 2).toUpperCase(),
            this.range
          );
        } else if (this.reg.GpReg == "RFlags" && this.range.start_byte == this.range.end_byte) {
          return [ "CF", "PF", "AF", "ZF", "SF", "OF" ][this.range.start_byte];
        }
      } else if (this.reg !== null && typeof(this.reg.X87) == 'string') {
        switch (this.reg.X87) {
          case 'TopOfStack': return 'TOP';
          case 'TagWord': return 'TAG';
          case 'ExceptionFlags': return 'EF';
          case 'ConditionCodes': return 'CC';
        }

        return this.reg.X87;
      }

      return null;
    },
  },
  methods: {},
};
</script>
<style scoped>
.reg {
  position: relative;
  display: flex;
}
</style>