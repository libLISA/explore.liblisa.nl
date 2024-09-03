<template>
  <form v-on:submit.prevent="submit" class="instruction-input">
    <input
      ref="input"
      type="search"
      autofocus
      :value="modelValue"
      @input="$emit('update:modelValue', $event.target.value)"
      pattern="([a-zA-Z0-9][a-zA-Z0-9] ?)+"
      :placeholder="placeholder"
    />
    <div class="reset">
      <input v-if="modelValue != ''" @click="reset" type="reset" value="&times;" alt="Clear the instruction" />
    </div>
  </form>
</template>

<script>
export default {
  name: "HelloWorld",
  props: {
    placeholder: String,
    modelValue: String,
  },
  methods: {
    submit() {},
    reset() {
      this.$emit('update:modelValue');
      this.$refs.input.focus();
    }
  },
  emits: ["submit", "update:modelValue"],
};
</script>

<style scoped>
.instruction-input {
  display: flex;
  flex-direction: row;
  margin: 8px;
  position: relative;
}

.instruction-input input {
  font-size: 2em;
}

input {
  flex-grow: 1;
  padding: 4px;
  text-align: center;
  font-family: monospace;
}

.reset {
  width: 0;
  position: relative;
}

input[type="reset"] {
  flex-grow: 0;
  aspect-ratio: 1 / 1;
  border: none;
  margin: 5px;
  padding: 0;
  height: calc(100% - 10px);

  position: absolute;
  right: 0;
}

input[type="reset"]:hover {
  background: #ddd;
  cursor: pointer;
}

.button {
  display: inline;
  padding: .2em 1.2em;
  background: #1c5dcf;
  color: #fff;
  border: 1px solid #1c5dcf;
  font-size: 1.2em;
  font-weight: 900;
}

.button:hover {
  background: #3498db;
  cursor: pointer;
}
</style>
