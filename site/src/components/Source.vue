<template>
  <span v-if="source !== undefined" class="source">
    <span v-if="source.Dest !== undefined">
      <Dest :dest="source.Dest" :chosen="chosen" />
    </span>
    <span v-else-if="source.Imm !== undefined">
      <Imm :value="source.Imm" :chosen="chosen" />
    </span>
    <span v-else-if="source.Const !== undefined">
      Const {{ source.value }}
    </span>
  </span>
  <span v-else> NULL </span>
</template>

<script>
import Dest from "./Dest.vue";
import Imm from "./Imm.vue";

export default {
  name: "Source",
  components: {
    Dest,
    Imm,
  },
  props: {
    source: Object,
    chosen: String,
  },
  computed: {},
  methods: {},
};
</script>
