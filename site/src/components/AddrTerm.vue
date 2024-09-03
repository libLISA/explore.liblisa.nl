<template>
  <span v-if="term.primary.shift.mult != 0" class="term">
    <template v-if="term.primary.shift.right != 0">(</template>
    <span v-if="term.primary.shift.mult != 1">
      {{ term.primary.shift.mult }} &times;
    </span>
    <slot />
    <template v-if="term.primary.shift.right != 0">)</template>
    <span v-if="term.primary.shift.right != 0"> >> {{ term.primary.shift.right }} </span>
    <span v-if="term.secondary != null">
      {{ term.secondary }}
    </span>
  </span>
</template>

<script>
export default {
  name: "AddrTerm",
  props: {
    term: Object,
  },
  computed: {},
  methods: {},
};
</script>

<style scoped>
.dest {
  display: inline-block;
  background: #1c5dcf;
  color: #fff;
  font-weight: 900;
  padding: 4px;
  margin: 2px 0;
  border-radius: 4px 4px;
}

.dest:hover {
  background: #689fff;
  cursor: pointer;
}
</style>
