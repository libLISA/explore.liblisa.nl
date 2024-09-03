<template>
  <span :class="['dest', 'input-component', chosen]"> 0x{{ hexValue }} </span>
</template>

<script>
export default {
  name: "Imm",
  props: {
    value: Number,
    chosen: String,
  },
  computed: {
    hexValue() {
      return this.value.toString(16);
    },
  },
  methods: {},
};
</script>

<style scoped></style>
