<template>
  <div :class="{
    'main': true,
    'presentation-highlight': presentationHighlight,
  }">
    <div v-if="info === null" class="content"></div>
    <div v-else class="content top">
      <div class="bits">
        <div class="bitpattern">
          <template v-for="(bit, index) in bits">
            <span
              :key="index"
              v-if="bit.Part !== undefined"
              @mouseover="hoversOverPart = bit.Part"
              @mouseleave="hoversOverPart = null"
              @click="toggleBit(index)"
              :class="{
                'bit-value': true,
                'part-hovered':
                  hoversOverPart == bit.Part || hoversOverPartBitsOnly == bit.Part,
                ['text-chosen' + bit.Part]: true,
              }"
            >
              <template v-if="hoversOverPart == bit.Part || hoversOverPartBitsOnly == bit.Part">
                {{ bitValues[index] }}
              </template>
              <template v-else>
                {{ ["a", "b", "c", "d", "e", "f", "g", "h"][bit.Part] }}
              </template>
            </span>
            <span
              :key="index + 1000"
              v-else-if="bit.Fixed !== undefined"
              @click="toggleBit(index)"
              class="bit-fixed"
              >{{ bit.Fixed }}</span
            >
            <span
              :key="index + 2000"
              v-else-if="bit == 'DontCare'"
              class="bit-fixed"
              >_</span
            >
          </template>
        </div>
      </div>
      <div class="parts" v-if="jsInfo.parts.length != 0">
        <h3>Parts</h3>
        <ul class="flow-list">
          <li
            :class="{
              hover: hoversOverPart == partIndex,
              ['override-chosen' + partIndex]: true,
            }"
            @mouseover="hoversOverPartBitsOnly = partIndex"
            @mouseleave="hoversOverPartBitsOnly = null"
            v-for="(part, partIndex) in jsInfo.parts"
            :key="partIndex"
          >
            <div :class="['background-chosen' + partIndex, 'partname']">
              {{
                ["a", "b", "c", "d", "e", "f", "g", "h"][partIndex]
              }}
            </div>
            <!-- <span> &nbsp;=&nbsp; </span> -->

            <input
              type="text"
              v-if="
                part.mapping.Imm !== undefined &&
                partValues[partIndex] !== undefined
              "
              :value="
                partValues[partIndex].toString(2).padStart(part.size, '0')
              "
              :minlength="part.size"
              :maxlength="part.size + 1"
            />

            <ul class="part-mapping" v-if="part.mapping.Register !== undefined">
              <li
                :class="{
                  'input-component': true,
                  disabled: mapping === null,
                  clickable: mapping !== null,
                  selected: partValues[partIndex] == index,
                }"
                v-for="(mapping, index) in part.mapping.Register.mapping"
                :key="index"
                @click="mapping !== null && choosePart(partIndex, index)"
              >
                <span class="tt bits">{{
                  index.toString(2).padStart(part.size, "0")
                }}</span>
                <span class="meaning">
                  <Reg v-if="mapping !== null" :reg="mapping" />
                  <span v-else>Invalid</span>
                </span>
              </li>
            </ul>

            <ul
              class="part-mapping"
              v-if="part.mapping.MemoryComputation !== undefined"
            >
              <li
                :class="{
                  'input-component': true,
                  clickable: true,
                  selected: partValues[partIndex] == index,
                }"
                v-for="(mapping, index) in part.mapping.MemoryComputation
                  .mapping"
                :key="index"
                @click="choosePart(partIndex, index)"
              >
                <span class="tt bits">{{
                  index.toString(2).padStart(part.size, "0")
                }}</span>
                <span class="meaning">
                  <span>
                    <span
                      v-for="(term, termIndex) in mapping.terms"
                      :key="termIndex"
                    >
                      <template
                        v-if="term.primary.shift.mult != 0 && termIndex > 0"
                      >
                        +
                      </template>
                      <AddrTerm :term="term">
                        {{ ["A", "B", "C", "D"][termIndex] }}
                      </AddrTerm>
                    </span>
                    <span class="tt" v-if="mapping.offset != 0">
                      + {{ mapping.offset }}
                    </span>
                  </span>
                </span>
              </li>
            </ul>
          </li>
        </ul>
      </div>
      <div class="dataflows">
        <div class="dataflows-memory-accesses">
          <h3>Memory accesses</h3>
          <ul class="memory-accesses flow-list">
            <li v-for="(access, index) in chosenAccesses" :key="index">
              <span>
                Addr(<strong
                  >m<sub>{{ index }}</sub></strong
                >) =

                <span
                  v-for="(term, termIndex) in access.calculation.terms"
                  :key="termIndex"
                >
                  <template v-if="term.primary.shift.mult != 0 && termIndex > 0">
                    +
                  </template>
                  <AddrTerm :term="term">
                    <Source
                      :source="access.inputs[termIndex].source"
                      :chosen="access.inputs[termIndex].class"
                    />
                  </AddrTerm>
                </span>
                <span class="tt" v-if="access.calculation.offset != 0">
                  + {{ access.calculation.offset }}
                </span>
              </span>
              <span class="extra"> ({{ access.size.end }} bytes) </span>
            </li>
          </ul>
        </div>

        <div class="dataflows-outputs">
          <div class="header-with-tabs-and-links">
            <h3>Output</h3>

            <h3 :class="{
              ['tab']: true,
              ['active']: tab == 'dataflows'
            }" @click="tab = 'dataflows'">Dataflows</h3>
            <h3 :class="{
              ['tab']: true,
              ['active']: tab == 'smt'
            }" @click="tab = 'smt'">SMTLib</h3>
            <!-- TODO: More exports -->
            <!-- <h3  :class="{
              ['tab']: true,
              ['active']: tab == 'python'
            }" @click="tab = 'python'">Python</h3> -->
            <!-- <h3  :class="{
              ['tab']: true,
              ['active']: tab == 'c'
            }" @click="tab = 'c'">C99</h3> -->
            <!-- <h3  :class="{
              ['tab']: true,
              ['active']: tab == 'rust'
            }" @click="tab = 'rust'">Rust</h3> -->

            <div v-if="tab == 'dataflows'" class="link" @click="showSimulate = !showSimulate">simulate ⬎</div>
          </div>
          <div class="popup" v-if="showSimulate">
            <p>
              Fill in the values below to see computed execution results in the outputs.
            </p>
            <ul class="values flow-list">
              <li
                v-for="(input, inputIndex) in simulationInputs"
                :key="inputIndex"
              >
                <strong><Dest :dest="input"/></strong>
                <span>&nbsp;=&nbsp;</span>

                <div class="input-with-error">
                  <input type="text" @input="simulationValues[JSON.stringify(input)] = $event.target.value" :value="simulationValues[JSON.stringify(input)]" :class="{
                    'error': simulationValueParsingErrors[JSON.stringify(input)] != undefined
                  }" />

                  <span v-if="simulationValueParsingErrors[JSON.stringify(input)] != undefined" class="error-text">
                    {{ simulationValueParsingErrors[JSON.stringify(input)] }}
                  </span>
                </div>
              </li>
            </ul>
            <button @click="showSimulate = !showSimulate">Close</button>
          </div>
          <ul v-if="tab == 'dataflows'" class="outputs flow-list">
            <li v-for="(output, outputIndex) in chosenOutputs" :key="outputIndex">
              <strong><Dest :dest="output.dest" :chosen="output.class" /></strong>
              <span>&nbsp;=&nbsp;</span>

              <span v-if="output.computation === null">
                <i>
                  f<sub>{{ outputIndex }}</sub>
                </i>
                (
                <Source
                  v-for="(input, index) in output.inputs"
                  :source="input.source"
                  :chosen="input.class"
                  :key="index"
                />
                )
              </span>
              <span v-else class="computation">
                <Computation
                  :computation="output.computation"
                  :inputs="output.inputs"
                />
                <span class="simulation-result" v-if="simulationResults[JSON.stringify(output.dest)] != undefined && simulationResults[JSON.stringify(output.dest)] != ''">
                =
                {{ simulationResults[JSON.stringify(output.dest)] }}
                </span>

                <span class="extra">
                  ({{ describeComputationOutput(output.computation) }})
                </span>
              </span>
            </li>
          </ul>
          <div v-if="tab == 'smt'">
            <div class="code" v-html="info.smt_code(instr).replaceAll('\n', '<br />')"></div>

            <!-- TODO: Z3 -->
            <!-- <h4>Z3 solver</h4>
            <p>
              Enter an expression to verify below:
            </p>
            <textarea :v-html="solverText"></textarea>
            <button>
              Verify with Z3 (TODO)
            </button> -->
          </div>
          <div v-else-if="tab == 'python'">
            <div class="code">
              cpu.rax = 5<br />
              cpu.rip = cpu.rip + 6<br />
              TODO...
            </div>
          </div>
          <div v-else-if="tab == 'c'">
            <div class="code">
              cpu->rax = 5;<br />
              cpu->rip = cpu->rip + 6;<br />
              TODO...
            </div>
          </div>
          <div v-else-if="tab == 'rust'">
            <div class="code">
              cpu.rax = 5<br />
              cpu.rip = cpu.rip.wrapping_add(6);<br />
              TODO...
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script>
import Source from "./Source.vue";
import Dest from "./Dest.vue";
import Reg from "./Reg.vue";
import AddrTerm from "./AddrTerm.vue";
import Computation from "./Computation.vue";
import { bytesToHex, hexToBytes, crop } from "../utils.js";


export default {
  name: "AnalysisResults",
  props: {
    instr: String,
    info: Object,
  },
  components: {
    Source,
    Dest,
    AddrTerm,
    Reg,
    Computation,
  },
  data() {
    return {
      hoversOverPart: null,
      hoversOverPartBitsOnly: null,
      simulationValues: {},
      showSimulate: false,
      tab: "dataflows",
      solverText: "(check-sat)\n(get-model)",
      presentationHighlight: false,
    };
  },
  created() {
    window.addEventListener('keydown', this.onKeyDown);
  },
  beforeDestroy() {
    window.removeEventListener('keydown', this.onKeyDown);
  },
  computed: {
    jsInfo() {
      return JSON.parse(this.info.json());
    },
    bits() {
      if (this.info != null) {
        return JSON.parse(this.info.bits()).slice().reverse();
      } else {
        return [];
      }
    },
    bitValues() {
      // TODO: Replace with liblisa-wasm
      let bytes = hexToBytes(this.instr);
      let bits = [];
      // console.log(bytes);
      for (const byte of bytes) {
        // console.log(byte);
        for (let b = 7; b >= 0; b--) {
          bits.push((byte >> b) & 1);
        }
      }

      return bits;
    },
    partValues() {
      // TODO: Replace with liblisa-wasm
      if (!this.info) {
        return [];
      }

      return this.info.part_values();
    },
    chosenAccesses() {
      if (!this.info) {
        return [];
      }

      let chosen = [];
      let accesses = this.jsInfo.dataflows.addresses.memory;

      for (let accessIndex = 0; accessIndex < accesses.length; accessIndex++) {
        const access = accesses[accessIndex];
        if (access === undefined) {
          return [];
        }

        let inputs = [];

        for (
          let inputIndex = 0;
          inputIndex < access.inputs.inputs.length;
          inputIndex++
        ) {
          // console.log(JSON.stringify(access.inputs.inputs[inputIndex]));
          inputs[inputIndex] = {
            class: undefined,
            source: access.inputs.inputs[inputIndex],
          };
        }

        chosen[accessIndex] = {
          class: undefined,
          inputs: inputs,
          calculation: access.calculation,
          size: access.size,
        };
      }

      for (let partIndex = 0; partIndex < this.jsInfo.parts.length; partIndex++) {
        const part = this.jsInfo.parts[partIndex];
        const value = this.partValues[partIndex];
        // TODO: Imm values
        if (part.mapping.Register !== undefined) {
          // console.log(part);
          for (const loc of part.mapping.Register.locations) {
            if (loc.MemoryAddress !== undefined) {
              let outputEntry = chosen[loc.MemoryAddress.memory_index];
              let inputEntry =
                outputEntry.inputs[loc.MemoryAddress.input_index];
              inputEntry.class = "chosen" + partIndex;
              // console.log(
              //   "Setting",
              //   JSON.stringify(inputEntry.source.Dest),
              //   "for",
              //   JSON.stringify(part)
              // );
              inputEntry.source = {
                Dest: {
                  Reg: [
                    part.mapping.Register.mapping[value],
                    inputEntry.source.Dest.Reg[1],
                  ],
                },
              };
            }
          }
        } else if (part.mapping.MemoryComputation !== undefined) {
          for (const memoryIndex of part.mapping.MemoryComputation
            .memory_indexes) {
            let outputEntry = chosen[memoryIndex];
            outputEntry.class = "chosen" + partIndex;
            outputEntry.calculation =
              part.mapping.MemoryComputation.mapping[value];
          }
        } else if (part.mapping.Imm !== undefined) {
          for (const loc of part.mapping.Imm.locations) {
            if (loc.MemoryAddress !== undefined) {
              let outputEntry = chosen[loc.MemoryAddress.memory_index];
              let inputEntry =
                outputEntry.inputs[loc.MemoryAddress.input_index];
              inputEntry.class = "chosen" + partIndex;
              // console.log(
              //   "Setting",
              //   JSON.stringify(inputEntry.source.Dest),
              //   "for",
              //   JSON.stringify(part)
              // );

              // TODO: Use bitorder to translate this to the right value!

              inputEntry.source = {
                Imm: value,
              };
            }
          }
        }
      }

      // console.log(JSON.stringify(chosen));

      return chosen;
    },
    chosenOutputs() {
      let chosen = [];

      for (
        let outputIndex = 0;
        outputIndex < this.jsInfo.dataflows.outputs.length;
        outputIndex++
      ) {
        const output = this.jsInfo.dataflows.outputs[outputIndex];
        let inputs = [];

        for (
          let inputIndex = 0;
          inputIndex < output.inputs.inputs.length;
          inputIndex++
        ) {
          // console.log(JSON.stringify(output.inputs.inputs[inputIndex]));
          inputs[inputIndex] = {
            class: undefined,
            source: output.inputs.inputs[inputIndex],
            currentValue: null,
          };
        }

        chosen[outputIndex] = {
          class: undefined,
          dest: output.target,
          inputs: inputs,
          computation: output.computation,
        };
      }

      for (let partIndex = 0; partIndex < this.jsInfo.parts.length; partIndex++) {
        const part = this.jsInfo.parts[partIndex];
        const value = this.partValues[partIndex];
        // TODO: Imm values
        if (part.mapping.Register !== undefined) {
          for (const loc of part.mapping.Register.locations) {
            if (loc.Output !== undefined) {
              let outputEntry = chosen[loc.Output];
              outputEntry.class = "chosen" + partIndex;
              outputEntry.dest = {
                Reg: [
                  part.mapping.Register.mapping[value],
                  outputEntry.dest.Reg[1],
                ],
              };
            } else if (loc.InputForOutput !== undefined) {
              let outputEntry = chosen[loc.InputForOutput.output_index];
              let inputEntry = outputEntry.inputs[loc.InputForOutput.input_index];
              inputEntry.class = "chosen" + partIndex;
              inputEntry.source = {
                Dest: {
                  Reg: [
                    part.mapping.Register.mapping[value],
                    inputEntry.source.Dest.Reg[1],
                  ],
                },
              };
            }
          }
        } else if (part.mapping.Imm !== undefined) {
          for (const loc of part.mapping.Imm.locations) {
            if (loc.InputForOutput !== undefined) {
              let outputEntry = chosen[loc.InputForOutput.output_index];
              let inputEntry =
                outputEntry.inputs[loc.InputForOutput.input_index];
              inputEntry.class = "chosen" + partIndex;
              // console.log(
              //   "Setting",
              //   JSON.stringify(inputEntry.source),
              //   "for",
              //   JSON.stringify(part)
              // );

              // TODO: Use bitorder to translate this to the right value!

              inputEntry.source = {
                Imm: value,
              };
            }
          }
        }
      }

      for (
        let outputIndex = 0;
        outputIndex < chosen.length;
        outputIndex++
      ) {
        const output = chosen[outputIndex];

        for (
          let inputIndex = 0;
          inputIndex < output.inputs.length;
          inputIndex++
        ) {
          const inputEntry = output.inputs[inputIndex];
          inputEntry.currentValue = this.parsedSimulationValues[JSON.stringify(inputEntry.source.Dest)];
        }
      }

      // console.log("Chosen outputs:", chosen);

      return chosen;
    },
    simulationInputs() {
      let inputs = JSON.parse(this.info.simulation_inputs());
      // console.log("Simulation inputs:", inputs);
      return inputs;
    },
    parsedSimulationValues() {
      let inputs = JSON.stringify(this.simulationValues);
      let parsed = JSON.parse(this.info.parse_simulation_values(inputs));
      console.log("Parsed simulation values: ", parsed);
      return parsed;
    },
    simulationValueParsingErrors() {
      let inputs = JSON.stringify(this.simulationValues);
      let errors = JSON.parse(this.info.get_parsing_errors(inputs));
      console.log("Parsing errors: ", errors);
      return errors;
    },
    simulationResults() {
      let inputs = JSON.stringify(this.simulationValues);
      let outputs = this.info.simulate(inputs);
      console.log("Simulation result: ", outputs);
      return JSON.parse(outputs);
    }
  },
  methods: {
    async runSolver() {
      const { init } = require('z3-solver');
      const {
        Z3, // Low-level C-like API
        Context, // High-level Z3Py-like API
      } = await init();
      let ctx = Context('main');
      let solver = ctx.Solver();

      alert("TODO: Not implemented");
    },
    choosePart(partIndex, newValue) {
      let values = this.partValues;
      values[partIndex] = newValue;

      let bytes = hexToBytes(this.instr).reverse();
      let ns = [];

      const numBits = bytes.length * 8;
      for (let bitIndex = 0; bitIndex < numBits; bitIndex++) {
        const bit = this.jsInfo.bits[bitIndex];
        if (bit.Part != undefined) {
          const i = bit.Part;
          const val = (values[i] >> ns[i]) & 1;
          const bitMask = 1 << bitIndex % 8;

          bytes[bitIndex >> 3] =
            (bytes[bitIndex >> 3] & ~bitMask) | (val << bitIndex % 8);

          values[i] |= val << ns[i];
          ns[i] = (ns[i] | 0) + 1;
        }
      }

      let newInstruction = bytesToHex(bytes.reverse());
      this.$emit("change", newInstruction);
    },
    toggleBit(bitIndex) {
      let bytes = hexToBytes(this.instr);
      bytes[bitIndex >> 3] = bytes[bitIndex >> 3] ^ (1 << (7 - bitIndex % 8));
      let newInstruction = bytesToHex(bytes);
      this.$emit("change", newInstruction);
    },
    describeComputationOutput(computation) {
      let endianness = "";
      let bits = 0;
      if (computation.output_type.Integer !== undefined) {
        bits = computation.output_type.Integer.num_bits;
      } else {
        bits = computation.output_type.Bytes.num_bytes * 8;
      }
      if (bits > 8 && computation.output_bytes) {
        if (computation.output_encoding == "UnsignedLittleEndian") {
          endianness = " little endian";
        } else {
          endianness = " big endian";
        }
      }

      return bits + " bit" + endianness;
    },
    onKeyDown(e) {
      console.log(e);
      var evtobj = window.event ? event : e;
      if (evtobj.code == 'F4') {
        this.presentationHighlight = !this.presentationHighlight;
      }
    }
  },
  emits: ["change"],
};
</script>

<!-- Add "scoped" attribute to limit CSS to this component only -->
<style scoped>
.main {
  display: flex;
  justify-content: center;
  margin: 0px 16px;
  flex-grow: 1;
}

@media only screen and (max-width: 720px) {
  .main {
    margin: 0px 2px;
  }
}

.content {
  display: flex;
  flex-direction: column;
  justify-content: center;
  max-width: 1200px;
  width: 100%;
}

.top {
  justify-self: flex-start;
  align-self: start;
}

.header {
  display: flex;
  flex-direction: row;
  align-self: center;
}

.bits {
  align-self: center;
}

.bits > * {
  align-self: center;
}

.bits > span {
  font-size: 1.5em;
}

.bits .bitpattern {
  display: inline-flex;
  flex-direction: row;
  font-family: monospace;
  font-size: 2.5em;
  align-self: center;
  padding-left: 0;
  flex-wrap: wrap;
  margin-top: 1em;
}

.bits .bitpattern > span {
  list-style: none;
  padding: 0;
}

.bits .bitpattern > span:nth-of-type(1) {
  margin-left: .2em;
}

.bits .bitpattern > span:nth-of-type(8n + 9) {
  margin-left: .4em;
}

.bits .bit-value {
  text-decoration: underline;
  font-weight: 900;
}

.bits .bit-value:hover,
.bits .bit-value.part-hovered {
  background: #eee;
}

.bit-value, .bit-fixed {
  cursor: pointer;
}

.dataflows,
.parts {
  text-align: left;
}

.outputs .computation {
  display: flex;
  flex-grow: 1;
  align-items: center;
}

.parts input,
.values input {
  font-family: monospace;
  border: 1px dashed #999;
  flex-grow: 1;
  background: none;
  font-size: 1.5em;
}

.input-with-error {
  display: flex;
  flex-direction: column;
  font-size: small;
  color: #a11;
}

input.error {
  border: 1px solid #f00;
  background: #fee;
}

.parts .flow-list li.hover {
  background: #bcceeb;
}

.memory-accesses li {
  display: flex;
}

.memory-accesses .extra,
.outputs .computation .extra {
  align-self: center;
  margin-left: auto;
  margin-right: 1em;
  color: #333;
  white-space: nowrap;
}

.simulation-result {
  align-self: center;
  font-family: monospace;
  font-size: 1.4em;
  margin: 0em 1em;
}

.part-mapping {
  display: inline-flex;
  flex-wrap: wrap;
  margin: 0.2em;
  padding: 0;
  row-gap: 0.4em;
}

.part-mapping li {
  margin: 0 0.2em;
  padding: 0;
  display: flex;
}

.part-mapping li .bits {
  background: rgba(0, 0, 0, .3);
  padding: 0px 6px;
  border-top-left-radius: 4px 4px;
  border-bottom-left-radius: 4px 4px;
  color: #eee;
  flex-grow: 0;
  height: 100%;
  align-items: center;
  display: flex;
}

.part-mapping li.disabled .bits {
  background: rgba(0, 0,0, .15);
}

.part-mapping li.selected .bits {
  color: #fff;
}

.part-mapping li .meaning {
  padding: 4px 6px;
  flex-grow: 1;
  justify-self: stretch;
  display: flex;
  align-items: center;
  position: relative;
  top: 2px;
}

p {
  color: #555;
}

.flow-list > li {
  padding: 0;
  min-height: 3em;
}

.flow-list > li > .partname {
  font-family: monospace;
  font-size: 1.5em;
  font-weight: 900;
  padding: .1em .4em;
  justify-self: stretch;
  display: flex;
  border-top-left-radius: 4px 4px;
  border-bottom-left-radius: 4px 4px;
  align-self: stretch;
  align-items: center;
}

.flow-list > li > input {
  margin: .5em;
}

.flow-list > li > ul {
  margin: .5em;
}

.header-with-tabs-and-links {
  display: flex;
  align-items: end;
  margin-bottom: 1.2em;
  margin-right: 1em;
}

.header-with-tabs-and-links h3 {
  flex-grow: 0;
  margin-bottom: 0;
  align-self: flex-start;
}

.header-with-tabs-and-links .link {
  text-decoration: underline;
  cursor: pointer;
  border: none;
  background: none;
  margin-left: auto;
}

.header-with-tabs-and-links {
  display: flex;
  margin-bottom: 1.2em;
  align-items: end;
  justify-content: start;
}

.header-with-tabs-and-links h3 {
  margin-bottom: 0;
}

.header-with-tabs-and-links .tab {
  color: #b2b7bb;
  margin-left: 10px;
  display: block;
  cursor: pointer;
  text-decoration: underline;
}

.header-with-tabs-and-links .tab:hover {
  color: #516376;
}

.header-with-tabs-and-links .tab.active {
  color: #2c3e50;
}

.popup {
  position: absolute;
  background: #fff;
  border: #aaa 1px solid;
  border-radius: 8px;
  box-shadow: rgba(0 0 0 / 50%) 4px 4px 40px;
  padding: 16px 32px 32px 32px;
  z-index: 100;
  right: 2em;
}

button {
  padding: 4px;
  width: 100%;
  border: 1px solid #aaa;
  background: #fff;
}

button:hover {
  background: #eee;
  cursor: pointer;
}

h4 {
  margin-bottom: 0;
}

textarea {
  width: 100%;
  height: 20em;
  font-family: monospace;
}
</style>

<style>
.code {
  display: block;
  border: solid 1px #ccc;
  background: #f8f8f8;
  padding: 1em;
  font-family: monospace;
}

.code .comment {
  color: #393;
}

.presentation-highlight .bitpattern:hover, .presentation-highlight .parts:hover, .presentation-highlight .dataflows-memory-accesses:hover, .presentation-highlight .dataflows-outputs:hover:not(:has(.flow-list:hover)), .presentation-highlight .dataflows-outputs .flow-list li:hover {
  background-color: rgb(199, 231, 255);
  box-shadow: rgb(199, 231, 255) 0 0 3px;
}
</style>