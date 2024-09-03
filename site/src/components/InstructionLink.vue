<template>
    <router-link :to="'/instruction/' + instr.toUpperCase()" @mouseover="prefetchInstr()">
        <slot></slot>
    </router-link>
</template>

<script>

export default {
  name: "InstructionLink",
  props: {
    instr: String,
  },
  methods: {
    async prefetchInstr() {
      let result = await this.$fetcher.search(this.instr);
      console.log("Prefetched:", result);
    }
  }
}
</script>