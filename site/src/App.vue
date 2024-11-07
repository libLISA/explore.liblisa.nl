<template>
  <div class="page">
    <div class="nav">
      <RouterLink to="/" class="entry left" v-if="$route.name == 'instruction'">
        ⮜ Back to start
      </RouterLink>
      <a class="entry right" href="https://liblisa.nl/">
        More info
      </a>
    </div>
    <RouterView />
  </div>
</template>

<script>
export default {
  name: "App",
  components: {},
};
</script>

<style>
html,
body {
  height: 100%;
  margin: 0;
  padding: 0;
  background: #ffffff;
}

#app {
  font-family: Avenir, Helvetica, Arial, sans-serif;
  -webkit-font-smoothing: antialiased;
  -moz-osx-font-smoothing: grayscale;
  text-align: center;
  color: #000;

  display: flex;
  flex-direction: column;
  flex-grow: 1;
  height: 100%;
  padding: 0;
  margin: 0;
}

.page {
  display: flex;
  flex-direction: column;
  flex-grow: 1;
  padding: 8px;
  padding-bottom: 3em;
}

.input-component {
  display: inline-block;
  background: #e1e1e1;
  color: #000;
  font-weight: 900;
  padding: 4px 6px;
  margin: 2px 2px;
  border-radius: 4px 4px;
  box-shadow: 1px 1px 2px rgba(0, 0, 0, 0.3);
}

.input-component.clickable:hover {
  background: #b6b6b6; /* #689fff; */
  cursor: pointer;
}

.input-component.selected {
  background: #1c5dcf;
  color: #fff;
}

.input-component.disabled {
  background: #f8f8f8;
  box-shadow: 1px 1px 2px rgba(0, 0, 0, 0.1);
  color: #ccc;
  cursor: default;
}

.input-component.chosen0,
.override-chosen0 .input-component.selected,
.background-chosen0 {
  background: #cf1c1c;
  color: #fff;
}

.input-component.chosen1,
.override-chosen1 .input-component.selected,
.background-chosen1,
.input-component.chosen1 .copy-chosen-bg,
.input-component.chosen1 + .copy-sibling-chosen-bg {
  background: #81cf1c;
  color: #fff;
}

.input-component.chosen2,
.override-chosen2 .input-component.selected,
.background-chosen2,
.input-component.chosen2 .copy-chosen-bg,
.input-component.chosen2 + .copy-sibling-chosen-bg {
  background: #671ccf;
  color: #fff;
}

.input-component.chosen3,
.override-chosen3 .input-component.selected,
.background-chosen3,
.input-component.chosen3 .copy-chosen-bg,
.input-component.chosen3 + .copy-sibling-chosen-bg {
  background: #79e9ff;
  color: #fff;
}

.input-component.chosen4,
.override-chosen4 .input-component.selected,
.background-chosen4,
.input-component.chosen4 .copy-chosen-bg,
.input-component.chosen4 + .copy-sibling-chosen-bg {
  background: #ba1ccf;
  color: #fff;
}

.input-component.chosen5,
.override-chosen5 .input-component.selected,
.background-chosen5,
.input-component.chosen5 .copy-chosen-bg,
.input-component.chosen5 + .copy-sibling-chosen-bg {
  background: #1c4ccf;
  color: #fff;
}

.text-chosen0 {
  color: #cf1c1c;
}

.text-chosen1 {
  color: #81cf1c;
}

.text-chosen2 {
  color: #671ccf;
}

.text-chosen3 {
  color: #79e9ff;
}

.text-chosen4 {
  color: #ba1ccf;
}

.text-chosen5 {
  color: #1c4ccf;
}

.flow-list {
  margin: 1em 0;
  padding-left: 1em;
  list-style: none;
}

.flow-list > li {
  padding: 0.5em;
  display: flex;
}

.flow-list > li > * {
  align-self: center;
}

.flow-list > li:nth-child(2n + 1) {
  background: rgba(0, 0, 0, 5%);
}

@media only screen and (max-width: 900px) {
  .flow-list {
    margin: 0;
    padding: 0;
  }

  .page {
    padding: 4px;
  }
}

.tt {
  font-family: monospace;
}

.nav {
  display: flex;
  border-bottom: 1px solid #eee;
  background: #1c5dcf;
  margin: -8px -8px 0 -8px;
  overflow: hidden;
  align-items: center;
  height: 2em;
}

.nav .entry.left {
  align-self: flex-start;
}

.nav .entry.right {
  margin-left: auto;
}

.nav button, .nav a {
  border: none;
  background: none;
  cursor: pointer;
  padding: 0px 12px;

  display: block;
  height: 100%;

  display: flex;
  align-items: center;

  color: #fff;
  text-decoration: none;
  text-shadow: -8px 0px 40px rgba(0 0 0 / 0%);
  transition: text-shadow .2s;
}

.nav button:hover, .nav a:hover {
  text-shadow: -8px 0px 40px rgba(0 0 0 / 100%);
  background: rgba(255 255 150 / 25%);
}

.notice {
  margin: 1em auto;
  background: #f0caca;
  font-weight: 900;
  border: 1px solid #cf1c1c;
  border-radius: 5px;
  box-shadow: 5px 5px 5px rgba(0 0 0 / 5%);
  padding: 16px;
  max-width: 800px;
}
</style>
