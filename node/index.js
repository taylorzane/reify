"use strict";

const runtime = require("../lib/runtime");
const parent = module.parent || __non_webpack_module__.parent;

runtime.enable(parent);
module.exports = exports = require("./compile-hook.js");
