<template>
  <span class="filledin">
      <span :class="['dest', 'input-component', chosen, 'hide-on-hover']"> {{ value }} </span>
      <Source class="hidden" :source="actualSource" :chosen="chosen" />
  </span>
</template>

<script>
import Source from "./Source.vue";
import Imm from "./Imm.vue";

export default {
  name: "FilledInSource",
  props: {
    value: String,
    chosen: String,
    actualSource: Object,
  },
  components: {
    Source,
    Imm,
  },
  computed: {
    hexValue() {
      return this.value.toString(16);
    },
  },
  methods: {},
};
</script>

<style scoped>
.filledin {
  display: inline-grid;
  align-items: center;
  justify-items: center;
}

.filledin > * {
  grid-column-start: 1;
  grid-row-start: 1;
}

.hidden {
  visibility: hidden;
}

.filledin:hover .hidden {
  visibility: visible;
}

.filledin:hover .hide-on-hover {
  visibility: hidden;
}
</style>
