var assert = require("assert");
var parse = require("reify/lib/parsers/babylon.js").parse;
var hasOwn = Object.prototype.hasOwnProperty;
var t = require("babel-types");

module.exports = function () {
  return {
    visitor: {
      Program: function (path) {
        var importExportState = {
          opts: this.opts,
          bodyPaths: [],
          removals: [],
          exportedLocalNames: Object.create(null),
          nextKey: 0
        };

        path.traverse(importExportVisitor, importExportState);

        path.traverse(assignmentVisitor, {
          exportedLocalNames: importExportState.exportedLocalNames,
        });

        finalizeHoisting(importExportState);
      }
    }
  };
};

var importExportVisitor = {
  ImportDeclaration: function (path) {
    var decl = path.node;
    var parts = [];

    if (decl.specifiers.length > 0) {
      if (this.opts.generateLetDeclarations) {
        parts.push("let ");
      } else {
        parts.push("var ");
      }

      decl.specifiers.forEach(function (s, i) {
        var isLast = i === decl.specifiers.length - 1;
        parts.push(s.local.name);
        if (s.type === "ImportNamespaceSpecifier") {
          // Initialize the local name for `* as local` specifiers so that
          // we don't have to initialize it in the setter function.
          parts.push("={}");
        }
        parts.push(isLast ? ";" : ",");
      });
    }

    parts.push(toModuleImport(
      JSON.stringify(decl.source.value),
      computeSpecifierMap(decl.specifiers),
      makeUniqueKey(this)
    ));

    hoistImports(this, path, parts.join(""));
  },

  ExportAllDeclaration: function (path) {
    var decl = path.node;
    var parts = [
      "module.import(",
      JSON.stringify(decl.source.value),
      ",{'*':function(v,k){exports[k]=v;}},",
      makeUniqueKey(this),
      ");",
    ];

    hoistExports(this, path, parts.join(""));
  },

  ExportDefaultDeclaration: function (path) {
    var decl = path.node;
    var dd = decl.declaration;

    if (dd.id && (dd.type === "FunctionDeclaration" ||
                  dd.type === "ClassDeclaration")) {
      // If the exported default value is a function or class declaration,
      // it's important that the declaration be visible to the rest of the
      // code in the exporting module, so we must avoid compiling it to a
      // named function or class expression.
      hoistExports(this, path, {
        "default": dd.id.name
      }, "declaration");

    } else {
      var declPath = path.get("declaration");

      this.visit(declPath); // TODO

      // A Function or Class declaration has become an expression on the
      // right side of the _exportDefaultPrefix assignment above so change
      // the AST appropriately
      if (dd.type === "FunctionDeclaration") {
        dd.type = "FunctionExpression";
      } else if (dd.type === "ClassDeclaration") {
        dd.type = "ClassExpression";
      }

      path.replaceWith(
        buildExportDefaultStatement(declPath.node)
      );
    }
  },

  ExportNamedDeclaration: function (path) {
    var decl = path.node;
    var dd = decl.declaration;

    if (dd) {
      var specifierMap = {};
      var addNameToMap = function (name) {
        specifierMap[name] = name;
      };

      if (dd.id && (dd.type === "ClassDeclaration" ||
                    dd.type === "FunctionDeclaration")) {
        addNameToMap(dd.id.name);
      } else if (dd.type === "VariableDeclaration") {
        dd.declarations.forEach(function (ddd) {
          getNamesFromPattern(ddd.id).forEach(addNameToMap);
        });
      }

      hoistExports(this, path, specifierMap, "declaration");
      addExportedLocalNames(this, specifierMap);

      return;
    }

    if (decl.specifiers) {
      var specifierMap = computeSpecifierMap(decl.specifiers, true);

      if (decl.source) {
        if (specifierMap) {
          var newMap = {};

          Object.keys(specifierMap).forEach(function (local) {
            newMap["exports." + local] = specifierMap[local];
          });

          specifierMap = newMap;
        }

        // Even though the compiled code uses module.import, it should
        // still be hoisted as an export, i.e. before actual imports.
        hoistExports(this, path, toModuleImport(
          JSON.stringify(decl.source.value),
          specifierMap,
          makeUniqueKey(this)
        ));

      } else {
        hoistExports(this, path, specifierMap);
        addExportedLocalNames(this, specifierMap);
      }
    }
  }
};

var assignmentVisitor = {
  AssignmentExpression: {
    exit: function (path) { // TODO Is exit really needed?
      return assignmentHelper(this, path, "left");
    }
  },

  UpdateExpression: {
    exit: function (path) {
      return assignmentHelper(this, path, "argument");
    }
  },

  CallExpression: {
    exit: function (path) {
      var callee = path.node.callee;
      if (callee.type === "Identifier" &&
          callee.name === "eval") {
        wrapAssignment(path);
      }
    }
  }
};

function assignmentHelper(visitor, path, childName) {
  var child = path.node[childName];
  var assignedNames = getNamesFromPattern(child);
  var modifiesExport = assignedNames.some(function (name) {
    return hasOwn.call(visitor.exportedLocalNames, name);
  });

  if (modifiesExport) {
    wrapAssignment(path);
  }
}

function wrapAssignment(path) {
  path.replaceWith(
    t.callExpression(t.memberExpression(
      t.identifier("module"),
      t.identifier("runModuleSetters")
    ), [path.node])
  );
}

function toModuleImport(source, specifierMap, uniqueKey) {
  var parts = ["module.import(", source];
  var locals = specifierMap && Object.keys(specifierMap);

  if (! locals || locals.length === 0) {
    parts.push(");");
    return parts.join("");
  }

  parts.push(",{");

  locals.forEach(function (local, i) {
    var isLast = i === locals.length - 1;
    var imported = specifierMap[local];
    var valueParam = safeParam("v", local);

    parts.push(
      JSON.stringify(imported),
      ":function(", valueParam
    );

    if (imported === "*") {
      // When the imported name is "*", the setter function may be called
      // multiple times, and receives an additional parameter specifying
      // the name of the property to be set.
      var nameParam = safeParam("n", local, valueParam);
      parts.push(
        ",", nameParam, "){",
        // The local variable should have been initialized as an empty
        // object when the variable was declared.
        local, "[", nameParam, "]=", valueParam
      );
    } else {
      parts.push("){", local, "=", valueParam);
    }

    parts.push(isLast ? "}" : "},");
  });

  parts.push("}," + uniqueKey + ");");

  return parts.join("");
}

var slice = Array.prototype.slice;

function safeParam(param) {
  var args = slice.call(arguments);
  if (args.indexOf(param, 1) < 0) {
    return param;
  }
  args[0] = "_" + param;
  return safeParam.apply(this, args);
}

function toModuleExport(specifierMap) {
  var exportedKeys = specifierMap && Object.keys(specifierMap);

  if (! exportedKeys ||
      exportedKeys.length === 0) {
    return "";
  }

  var parts = ["module.export({"];

  exportedKeys.forEach(function (exported, i) {
    var isLast = i === exportedKeys.length - 1;
    var local = specifierMap[exported];

    parts.push(
      exported,
      ":function(){return ",
      local,
      isLast ? "}" : "},"
    );
  });

  parts.push("});");

  return parts.join("");
}

// If inverted is true, the local variable names will be the values of the
// map instead of the keys.
function computeSpecifierMap(specifiers, inverted) {
  var specifierMap;

  specifiers.forEach(function (s) {
    var local = s.local.name;
    var __ported = // The IMported or EXported name.
      s.type === "ImportSpecifier" ? s.imported.name :
      s.type === "ImportDefaultSpecifier" ? "default" :
      s.type === "ImportNamespaceSpecifier" ? "*" :
      s.type === "ExportSpecifier" ? s.exported.name :
      null;

    if (typeof local !== "string" ||
        typeof __ported !== "string") {
      return;
    }

    specifierMap = specifierMap || {};

    if (inverted === true) {
      specifierMap[__ported] = local;
    } else {
      specifierMap[local] = __ported;
    }
  });

  return specifierMap;
}

function makeUniqueKey(visitor) {
  return visitor.nextKey++;
}

function hoistImports(visitor, importDeclPath, hoistedCode, childName) {
  // Calling this.preserveChild may remove importDeclPath from the AST,
  // so we must record its .parentPath first.
  var pp = importDeclPath.parentPath;
  preserveChild(visitor, importDeclPath, childName);
  var bodyPath = getBlockBodyPath(visitor, pp);
  bodyPath._hoistedImportsString += hoistedCode;
  return visitor;
}

function preserveChild(visitor, path, childName) {
  if (childName) {
    var childPath = path.get(childName);

    // Replace the given path with the child we want to preserve.
    path.replaceWith(childPath.node);

    visitor.visit(childPath); // TODO

  } else {
    // Schedule visitor path to be completely removed in finalizeHoisting.
    visitor.removals.push(path);
  }

  return visitor;
}

function getBlockBodyPath(visitor, path) {
  var stmtPath = path;
  var body;

  while (stmtPath) {
    if (stmtPath.node.type === "Program") {
      body = stmtPath.node.body;
      break;
    }

    if (stmtPath.node.type === "BlockStatement") {
      body = stmtPath.node.body;
      break;
    }

    if (stmtPath.node.type === "SwitchCase") {
      body = stmtPath.node.consequent;
      break;
    }

    if (t.isStatement(stmtPath.node)) {
      stmtPath.replaceWith(
        t.blockStatement([
          stmtPath.node
        ])
      );

      body = stmtPath.node.body;

      break;
    }

    stmtPath = stmtPath.parentPath;
  }

  // Avoid hoisting above string literal expression statements such as
  // "use strict", which may depend on occurring at the beginning of
  // their enclosing scopes.
  var insertNodeIndex = 0;
  body.some(function (stmt, i) {
    if (stmt.type === "ExpressionStatement") {
      var expr = stmt.expression;
      if (expr.type === "StringLiteral" ||
          (expr.type === "Literal" &&
           typeof expr.node === "string")) {
        insertNodeIndex = i + 1;
        return;
      }
    }
    return true;
  });

  var bodyPath = stmtPath._bodyPath = stmtPath._bodyPath || {};

  if (hasOwn.call(bodyPath, "insertNodeIndex")) {
    assert.strictEqual(bodyPath.insertNodeIndex, insertNodeIndex);

  } else {
    bodyPath.nodes = body;
    bodyPath.insertNodeIndex = insertNodeIndex;
    bodyPath.hoistedExportsMap = Object.create(null);
    bodyPath.hoistedExportsString = "";
    bodyPath.hoistedImportsString = "";

    visitor.bodyPaths.push(bodyPath);
  }

  return bodyPath;
}

function finalizeHoisting(state) {
  state.bodyPaths.forEach(function (bodyPath) {
    var parts = [];

    var namedExports = toModuleExport(bodyPath.hoistedExportsMap);
    if (namedExports) {
      parts.push(namedExports);
    }

    if (bodyPath.hoistedExportsString) {
      parts.push(bodyPath.hoistedExportsString);
    }

    if (bodyPath._hoistedImportsString) {
      parts.push(bodyPath.hoistedImportsString);
    }

    if (parts.length > 0) {
      var codeToInsert = parts.join("");

      var ast = parse(codeToInsert);
      if (ast.type === "File") ast = ast.program;
      assert.strictEqual(ast.type, "Program");

      var spliceArgs = ast.body;
      spliceArgs.unshift(bodyPath.insertNodeIndex, 0);

      // TODO Make sure this works!
      bodyPath.nodes.splice.apply(bodyPath.nodes, spliceArgs);
    }

    delete bodyPath.nodes;
    delete bodyPath.insertCharIndex;
    delete bodyPath.insertNodeIndex;
    delete bodyPath.hoistedExportsMap;
    delete bodyPath.hoistedExportsString;
    delete bodyPath.hoistedImportsString;
  });

  // Just in case we call finalizeHoisting again, don't hoist anything.
  state.bodyPaths.length = 0;

  state.removals.forEach(function (declPath) {
    declPath.remove();
  });

  // Just in case we call finalizeHoisting again, don't remove anything.
  state.removals.length = 0;
}

var exportDefaultPrefix = 'module.export("default",exports.default=(';
var exportDefaultSuffix = "));";

function buildExportDefaultStatement(declaration) {
  var ast = parse(exportDefaultPrefix + "VALUE" + exportDefaultSuffix);
  if (ast.type === "File") ast = ast.program;
  assert.strictEqual(ast.type, "Program");

  var stmt = ast.body[0];
  assert.strictEqual(stmt.type, "ExpressionStatement");
  assert.strictEqual(stmt.expression.type, "CallExpression");

  var arg1 = stmt.expression.arguments[1];
  assert.strictEqual(arg1.right.type, "Identifier");
  assert.strictEqual(arg1.right.name, "VALUE");

  // Replace the VALUE identifier with the desired declaration.
  arg1.right = declaration;

  return stmt;
}

function addExportedLocalNames(visitor, specifierMap) {
  if (specifierMap) {
    var exportedLocalNames = visitor.exportedLocalNames;
    Object.keys(specifierMap).forEach(function (exported) {
      var local = specifierMap[exported];
      // It's tempting to record the exported name as the value here,
      // instead of true, but there can be more than one exported name per
      // local variable, and we don't actually use the exported name(s) in
      // the assignmentVisitor, so it's not worth the added complexity of
      // tracking unused information.
      exportedLocalNames[local] = true;
    });
  }
}

function getNamesFromPattern(pattern) {
  var queue = [pattern];
  var names = [];

  for (var i = 0; i < queue.length; ++i) {
    var pattern = queue[i];
    if (! pattern) {
      continue;
    }

    switch (pattern.type) {
    case "Identifier":
      names.push(pattern.name);
      break;
    case "Property":
    case "ObjectProperty":
      queue.push(pattern.value);
      break;
    case "AssignmentPattern":
      queue.push(pattern.left);
      break;
    case "ObjectPattern":
      queue.push.apply(queue, pattern.properties);
      break;
    case "ArrayPattern":
      queue.push.apply(queue, pattern.elements);
      break;
    case "RestElement":
      queue.push(pattern.argument);
      break;
    }
  }

  return names;
}
