import { createApp } from "vue";
import App from "./App.vue";
import InstructionView from "./InstructionView.vue"
import SearchView from "./SearchView.vue"
import ComparisonTableView from "./ComparisonTableView.vue"
import { createRouter, createWebHistory } from 'vue-router';

import init, { EncodingFetcher } from 'liblisa-wasm'
await init();

const routes = [
    { path: '/', name: 'home', component: SearchView },
    { path: '/search', name: 'search', component: SearchView },
    { path: '/architecture-comparison', name: 'architecture-comparison', component: ComparisonTableView },
    { path: '/instruction/:instr', name: 'instruction', component: InstructionView },
];

const router = createRouter({
    history: createWebHistory(),
    routes,
})

let app = createApp(App);
app.config.globalProperties.$fetcher = new EncodingFetcher("/data/");
app
    .use(router)
    .mount("#app");