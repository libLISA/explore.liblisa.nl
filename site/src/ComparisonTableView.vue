<template>
    <h1>Architecture comparison</h1>

    <table>
      <thead>
        <tr>
          <td>Group</td>
          <td>A0</td>
          <td>A1</td>
          <td>A2</td>
          <td>A3</td>
          <td>A4</td>
        </tr>
      </thead>
      <tbody>
        <tr v-for="(row, index) in rows">
          <td>Group {{ index }}</td>
          <td v-for="n in row.symbols()">{{ n }}</td>
        </tr>
      </tbody>
    </table>
</template>


<script>
export default {
  name: "ComparisonTableView",
  components: {
  },
  data() {
    return {
        rows: [],
    };
  },
  async created() {
    let table = await this.$fetcher.fetch_table();
    this.rows = table.into_rows();
  }
};
</script>

<style scoped>
table {
  border: 1px solid #000;
  margin: auto;
}

thead {
  font-weight: 900;
}
</style>