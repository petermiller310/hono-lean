#!/usr/bin/env node
/** Structural coverage inventory. This scanner is evidence, never a source proof. */
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { createRequire } from 'node:module';
import { fileURLToPath, pathToFileURL } from 'node:url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);
const EXPECTED_TYPESCRIPT = '6.0.3';
const slash = p => p.split(path.sep).join('/');
const hash = value => crypto.createHash('sha256').update(value).digest('hex');
const sorted = values => [...new Set(values)].sort();
const compare = (a,b) => a < b ? -1 : a > b ? 1 : 0;
const isSource = p => /\.(?:ts|tsx|mts|cts)$/.test(p);
const isTest = p => /(?:\.test\.|\.case\.test\.)/.test(p);
const evidence = () => ({ modelProof: 'not_mapped', sourceConnection: 'absent', conformance: 'not_run_for_this_unit', contractOutcome: 'pending' });

export function loadTypeScript(explicit) {
  let resolved;
  try { resolved = require.resolve(explicit || process.env.HONO_TYPESCRIPT || 'typescript'); }
  catch { throw new Error('TypeScript 6.0.3 required: run npm ci in verification/, or pass --typescript /path/to/typescript.'); }
  const ts = require(resolved);
  if (ts.version !== EXPECTED_TYPESCRIPT) throw new Error(`Expected TypeScript ${EXPECTED_TYPESCRIPT}; got ${ts.version}`);
  return { ts, metadata: { name: 'typescript', version: ts.version, implementationSha256: hash(fs.readFileSync(resolved)) } };
}

export function verifyCheckout(root, target) {
  const git = (...args) => execFileSync('git', ['-C', root, ...args], { encoding: 'utf8' }).trim();
  if (git('rev-parse', 'HEAD') !== target.revision) throw new Error(`Hono checkout is not pinned revision ${target.revision}`);
  const status = git('status', '--porcelain', '--untracked-files=all');
  if (status) throw new Error(`Hono checkout must be clean, including untracked files:\n${status}`);
  const files = git('ls-tree', '-r', '--name-only', target.revision).split('\n').filter(Boolean);
  // A clean checkout may still have automatic newline conversions; compare bytes.
  for (const p of files.filter(p => p === 'package.json' || (p.startsWith('src/') && isSource(p)))) {
    const expected = execFileSync('git', ['-C', root, 'show', `${target.revision}:${p}`]);
    if (!fs.readFileSync(path.join(root, p)).equals(expected)) throw new Error(`Working bytes differ from pinned Git blob: ${p}`);
  }
  return files;
}

function artifactSource(importTarget, files) {
  if (!importTarget?.startsWith('./dist/') || !importTarget.endsWith('.js')) throw new Error(`Unsupported artifact mapping: ${importTarget}`);
  const stem = 'src/' + importTarget.slice('./dist/'.length, -3);
  const hits = ['.ts', '.tsx', '.mts', '.cts'].map(e => stem + e).filter(p => files.includes(p));
  if (hits.length !== 1) throw new Error(`Expected one source for ${importTarget}; found ${hits.join(', ') || 'none'}`);
  return hits[0];
}

export function expandExports(exports, files) {
  const result = [];
  for (const [key, targets] of Object.entries(exports)) {
    if (typeof targets !== 'object' || typeof targets.import !== 'string') throw new Error(`Unsupported export conditions: ${key}`);
    if (!key.includes('*')) {
      result.push({ entryPoint: key, exportPattern: key, source: artifactSource(targets.import, files), targets });
      continue;
    }
    if ((key.match(/\*/g) || []).length !== 1 || (targets.import.match(/\*/g) || []).length !== 1) throw new Error(`Unsupported wildcard: ${key}`);
    const [prefix, suffix] = targets.import.split('*');
    if (!prefix.startsWith('./dist/') || suffix !== '.js') throw new Error(`Unsupported wildcard target: ${targets.import}`);
    const sourcePrefix = 'src/' + prefix.slice('./dist/'.length);
    for (const p of files.filter(p => p.startsWith(sourcePrefix) && isSource(p) && !isTest(p)).sort()) {
      const middle = p.slice(sourcePrefix.length).replace(/\.(?:ts|tsx|mts|cts)$/, '');
      const expanded = key.replace('*', middle);
      // An explicit key takes precedence over a matching wildcard.
      if (Object.hasOwn(exports, expanded)) continue;
      result.push({ entryPoint: expanded, exportPattern: key, source: p,
        targets: Object.fromEntries(Object.entries(targets).map(([condition, value]) => [condition, value.replace('*', middle)])) });
    }
  }
  return result.sort((a, b) => compare(a.entryPoint,b.entryPoint));
}

export function scanProject(root, fileList, ts, exportEntries) {
  const abs = p => path.join(root, p);
  const rel = p => slash(path.relative(root, p));
  const sourceFiles = fileList.filter(p => p.startsWith('src/') && isSource(p) && !isTest(p)).sort();
  const testFiles = fileList.filter(p => isSource(p) && isTest(p)).sort();
  const sourceSet = new Set(sourceFiles);
  const options = { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext,
    moduleResolution: ts.ModuleResolutionKind.Bundler, jsx: ts.JsxEmit.ReactJSX,
    jsxImportSource: 'hono/jsx', skipLibCheck: true, noEmit: true, types: [],
    baseUrl: root, paths: Object.fromEntries(exportEntries.map(e=>[e.entryPoint==='.'?'hono':'hono'+e.entryPoint.slice(1),[e.source]])) };
  const host = ts.createCompilerHost(options);
  const resolve = (specifier, containing) => {
    if (!specifier.startsWith('.') && specifier !== 'hono' && !specifier.startsWith('hono/')) return undefined;
    return ts.resolveModuleName(specifier, containing, options, host).resolvedModule;
  };
  // External package installations cannot quietly change the checked-in ledger.
  host.resolveModuleNames = (names, containing) => names.map(s => resolve(s, containing));
  const program = ts.createProgram(sourceFiles.map(abs), options, host);
  const syntax = program.getSyntacticDiagnostics().filter(d => d.category === ts.DiagnosticCategory.Error);
  if (syntax.length) throw new Error(`TypeScript syntax errors: ${syntax.map(d => ts.flattenDiagnosticMessageText(d.messageText, ' ')).join('; ')}`);
  const checker = program.getTypeChecker();
  const gaps = [];
  const location = node => { const sf = node.getSourceFile(); const start = node.getStart(sf); return { source: rel(sf.fileName), line: sf.getLineAndCharacterOfPosition(start).line + 1, start, end: node.end }; };
  const lexicalClassStart = node => { for(let p=node.parent;p;p=p.parent)if(ts.isClassDeclaration(p)||ts.isClassExpression(p))return p.getStart(p.getSourceFile());return null; };
  const text = node => node.getText(node.getSourceFile());
  const modifiers = node => new Set((ts.canHaveModifiers(node) ? ts.getModifiers(node) || [] : []).map(x => x.kind));
  const unwrap = node => { while (node && (ts.isAsExpression(node) || ts.isTypeAssertionExpression(node) || ts.isParenthesizedExpression(node) || ts.isSatisfiesExpression(node))) node = node.expression; return node; };
  const typeOnlyAlias = symbol => (symbol.declarations || []).some(d => {
    for (let n = d; n && !ts.isSourceFile(n); n = n.parent) {
      if ((ts.isExportSpecifier(n) || ts.isExportDeclaration(n) || ts.isImportSpecifier(n) || ts.isImportClause(n) || ts.isImportEqualsDeclaration(n)) && n.isTypeOnly) return true;
    }
    return false;
  });
  const resolveSymbol = symbol => {
    const seen = new Set();
    while (symbol && (symbol.flags & ts.SymbolFlags.Alias) && !seen.has(symbol)) { seen.add(symbol); symbol = checker.getAliasedSymbol(symbol); }
    return symbol;
  };
  const declarationInfo = declaration => ({ ...location(declaration), kind: ts.SyntaxKind[declaration.kind], name: declaration.name ? text(declaration.name) : null,
    sha256: hash(text(declaration)) });
  const brief = value => value.length > 350 ? { text: value.slice(0, 350), truncated: true } : { text: value, truncated: false };
  function parameters(declaration) {
    return (declaration.parameters || []).map(p => {
      let props = [], hostMembers = false;
      const ty = checker.getTypeAtLocation(p);
      const flatten = t => t.isUnionOrIntersection?.() ? t.types.flatMap(flatten) : [t];
      const candidates = flatten(ty);
      for (const t of candidates) if (t.flags & ts.TypeFlags.Object) {
        for (const s of checker.getPropertiesOfType(t)) {
          const ds=(s.declarations||[]).filter(d=>d.getSourceFile().fileName.startsWith(root+path.sep));
          if(!ds.length){hostMembers=true;continue;}
          props.push({name:s.name,declaredOptionalVariants:sorted(ds.map(d=>d.questionToken?'optional':'required')),declarations:ds.map(declarationInfo)});
        }
      }
      const merged=new Map();
      for(const prop of props){const old=merged.get(prop.name);if(old){old.declarations.push(...prop.declarations);old.declaredOptionalVariants=sorted([...old.declaredOptionalVariants,...prop.declaredOptionalVariants]);}else merged.set(prop.name,prop);}
      props = [...merged.values()].map(p=>({...p,declarations:[...new Map(p.declarations.map(d=>[d.source+':'+d.start,d])).values()]})).sort((a,b) => compare(a.name,b.name));
      return { name: text(p.name), optional: Boolean(p.questionToken || p.initializer), rest: Boolean(p.dotDotDotToken),
        declaredType: p.type ? brief(text(p.type)) : null, defaultExpression: p.initializer ? brief(text(p.initializer)) : null,
        declaredObjectProperties: props, hostOrIntrinsicMembersPresent:hostMembers,
        hostTypeAssumption:hostMembers?'external_type_model_required':null,runtimeDomain: 'not_specified_by_this_scan' };
    });
  }
  function constant(node, seen = new Set()) {
    node = unwrap(node);
    if (!node) return null;
    if (ts.isStringLiteralLike(node) || ts.isNumericLiteral(node)) return node.text;
    if (ts.isArrayLiteralExpression(node)) {
      const values = [];
      for (const child of node.elements) { const v = constant(ts.isSpreadElement(child) ? child.expression : child, seen); if (v === null) return null; values.push(...(ts.isSpreadElement(child) ? v : [v])); }
      return values;
    }
    if (ts.isIdentifier(node)) {
      const s = resolveSymbol(checker.getSymbolAtLocation(node));
      if (!s || seen.has(s)) return null;
      const d = s.valueDeclaration || s.declarations?.[0];
      return d && ts.isVariableDeclaration(d) ? constant(d.initializer, new Set([...seen,s])) : null;
    }
    return null;
  }
  function computedNames(node) {
    const expression = unwrap(node);
    if (ts.isStringLiteralLike(expression)) return [expression.text];
    if (ts.isIdentifier(expression)) {
      // Resolve a callback parameter over a syntactically constant forEach list.
      for (let p = expression.parent; p; p = p.parent) if (ts.isArrowFunction(p) || ts.isFunctionExpression(p)) {
        if (!p.parameters.some(x => ts.isIdentifier(x.name) && x.name.text === expression.text)) continue;
        const call = p.parent;
        if (ts.isCallExpression(call) && ts.isPropertyAccessExpression(call.expression) && call.expression.name.text === 'forEach') {
          const v = constant(call.expression.expression);
          if (Array.isArray(v) && v.every(x => typeof x === 'string')) return sorted(v);
        }
      }
      const v = constant(expression); if (typeof v === 'string') return [v];
    }
    return null;
  }
  const dependencies = new Map(), modules = new Map(), dynamicSites = [];
  const sourceNodes = new Map(sourceFiles.map(p => [p, program.getSourceFile(abs(p))]));
  for (const [p, sf] of sourceNodes) {
    const edges = [], declarations = [], dynamics = [];
    function dependency(specifier, phase, node, kind) {
      const found = resolve(specifier, sf.fileName);
      const internal = found && rel(found.resolvedFileName);
      if ((specifier.startsWith('.') || specifier === 'hono' || specifier.startsWith('hono/')) && (!internal || !sourceSet.has(internal))) throw new Error(`Unresolved/out-of-scope internal module ${p}: ${specifier}`);
      edges.push({ specifier, phase, kind, target: internal || null, ...location(node) });
      if (!internal) gaps.push({ kind:'external_import_contract', source:p, specifier, line:location(node).line });
    }
    function visit(node) {
      if (ts.isImportDeclaration(node) && ts.isStringLiteral(node.moduleSpecifier)) {
        const clause = node.importClause;
        const only = clause?.isTypeOnly || (clause?.namedBindings && ts.isNamedImports(clause.namedBindings) && !clause.name && clause.namedBindings.elements.every(e => e.isTypeOnly));
        dependency(node.moduleSpecifier.text, only ? 'type_only' : 'runtime_or_mixed', node, 'import');
      }
      if (ts.isExportDeclaration(node) && node.moduleSpecifier && ts.isStringLiteral(node.moduleSpecifier)) dependency(node.moduleSpecifier.text, node.isTypeOnly ? 'type_only' : 'runtime_or_mixed', node, 'reexport');
      if (ts.isImportTypeNode(node) && ts.isLiteralTypeNode(node.argument) && ts.isStringLiteral(node.argument.literal)) dependency(node.argument.literal.text, 'type_only', node, 'import_type');
      if (ts.isCallExpression(node) && (node.expression.kind === ts.SyntaxKind.ImportKeyword || (ts.isIdentifier(node.expression) && node.expression.text === 'require'))) {
        const arg = node.arguments[0]; const value = arg && constant(arg);
        if (typeof value === 'string') dependency(value, 'runtime_or_mixed', node, 'dynamic_import');
        else { const gap = { kind:'unresolved_dynamic_import', ...location(node), expression:brief(text(node)) }; gaps.push(gap); dynamics.push(gap); }
      }
      if ((ts.isFunctionDeclaration(node) || ts.isClassDeclaration(node) || ts.isInterfaceDeclaration(node) || ts.isTypeAliasDeclaration(node) || ts.isEnumDeclaration(node) || ts.isModuleDeclaration(node)) && node.name) declarations.push(declarationInfo(node));
      if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name)) declarations.push({ ...declarationInfo(node), initializerKind: node.initializer ? ts.SyntaxKind[unwrap(node.initializer).kind] : null });
      if (ts.isMethodDeclaration(node) || ts.isGetAccessorDeclaration(node) || ts.isSetAccessorDeclaration(node) || ts.isConstructorDeclaration(node) || ts.isPropertyDeclaration(node) || ts.isPropertySignature(node)) declarations.push({...declarationInfo(node),visibility:node.name&&ts.isPrivateIdentifier(node.name)?'javascript_private':modifiers(node).has(ts.SyntaxKind.PrivateKeyword)?'typescript_private_runtime_present':modifiers(node).has(ts.SyntaxKind.ProtectedKeyword)?'typescript_protected_runtime_present':'public_or_internal'});
      if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isElementAccessExpression(node.left)) {
        const names = computedNames(node.left.argumentExpression);
        const site = { kind:'computed_property_assignment', ...location(node), lexicalClassStart:lexicalClassStart(node), expression:brief(text(node.left)), resolvedNames:names,
          assignedKind:ts.SyntaxKind[unwrap(node.right).kind],parameters:parameters(unwrap(node.right)),
          nameResolutionBasis:'syntactic initializer/callback analysis; aliasing and mutations are not proved',nameResolutionExhaustive:false,review:'behavior_contract_pending' };
        dynamics.push(site);gaps.push({kind:names?'computed_property_behavior_pending':'unresolved_computed_property',...location(node),expression:brief(text(node.left))});
      }
      if(ts.isBinaryExpression(node)&&node.operatorToken.kind===ts.SyntaxKind.EqualsToken&&ts.isPropertyAccessExpression(node.left)&&node.left.expression.kind===ts.SyntaxKind.ThisKeyword){
        const site={kind:'instance_field_assignment',...location(node),lexicalClassStart:lexicalClassStart(node),expression:brief(text(node.left)),resolvedNames:[node.left.name.text],assignedKind:ts.SyntaxKind[unwrap(node.right).kind],parameters:parameters(unwrap(node.right)),review:'behavior_contract_pending'};
        dynamics.push(site);
      }
      if (ts.isCallExpression(node) && ts.isPropertyAccessExpression(node.expression) &&
          ['Object.assign','Object.defineProperty','Object.defineProperties','Reflect.set','Reflect.defineProperty'].includes(text(node.expression))) {
        const site = {kind:'reflective_property_update',...location(node),expression:brief(text(node)),review:'behavior_contract_pending'};
        dynamics.push(site); gaps.push(site);
      }
      if (ts.isNewExpression(node) && text(node.expression) === 'Proxy') { const site={kind:'proxy_generated_api',...location(node),expression:brief(text(node)),review:'runtime_surface_unbounded_pending_contract'};dynamics.push(site);gaps.push(site); }
      ts.forEachChild(node,visit);
    }
    visit(sf);
    dependencies.set(p,edges); dynamicSites.push(...dynamics);
    const js=sf.isDeclarationFile?'':ts.transpileModule(sf.text,{compilerOptions:{...options,noEmit:false},fileName:sf.fileName}).outputText;
    const emitted=ts.createSourceFile('emitted.js',js,ts.ScriptTarget.ES2022,true,ts.ScriptKind.JS);
    const markerOnly=emitted.statements.every(s=>ts.isExportDeclaration(s)&&!s.moduleSpecifier&&s.exportClause&&ts.isNamedExports(s.exportClause)&&s.exportClause.elements.length===0);
    modules.set(p,{source:p,sha256:hash(sf.text),classification:markerOnly?'erased_type_only':'runtime_or_mixed',
      classificationBasis:'TypeScript6.0.3 isolated transpilation inspection; not a semantics proof',
      declarations:declarations.sort((a,b)=>a.start-b.start),dependencies:edges,dynamicSites:dynamics,upstreamTests:[],evidence:evidence()});
  }
  const exportMemo=new Map();
  function runtimeExport(p,name,visiting=new Set()){
    const key=p+'#'+name;if(visiting.has(key))return false;const next=new Set([...visiting,key]);
    const sf=sourceNodes.get(p),mod=checker.getSymbolAtLocation(sf),symbol=mod&&checker.getExportsOfModule(mod).find(s=>s.name===name);
    if(!symbol)return false;const real=resolveSymbol(symbol);if(!(real?.flags&ts.SymbolFlags.Value))return false;
    for(const node of sf.statements)if(ts.isExportDeclaration(node)&&node.exportClause){
      if(ts.isNamespaceExport(node.exportClause)&&node.exportClause.name.text===name)return !node.isTypeOnly;
      if(ts.isNamedExports(node.exportClause))for(const spec of node.exportClause.elements)if(spec.name.text===name){
        if(node.isTypeOnly||spec.isTypeOnly)return false;
        if(node.moduleSpecifier){const e=dependencies.get(p).find(e=>e.start===node.getStart(sf));return Boolean(e?.target&&runtimeExport(e.target,spec.propertyName?.text||spec.name.text,next));}
        const local=checker.getExportSpecifierLocalTargetSymbol(spec);return !typeOnlyAlias(local||symbol)&&Boolean(resolveSymbol(local||symbol)?.flags&ts.SymbolFlags.Value);
      }
    }
    if((symbol.declarations||[]).some(d=>d.getSourceFile()===sf)&&!typeOnlyAlias(symbol))return true;
    return sf.statements.some(node=>{if(!ts.isExportDeclaration(node)||node.exportClause||node.isTypeOnly||!node.moduleSpecifier||name==='default')return false;const e=dependencies.get(p).find(e=>e.start===node.getStart(sf));return Boolean(e?.target&&runtimeExport(e.target,name,next));});
  }
  function exportPhases(p, visiting=new Set()) {
    if(exportMemo.has(p))return exportMemo.get(p);
    if(visiting.has(p))return new Map();
    const sf=sourceNodes.get(p), moduleSymbol=checker.getSymbolAtLocation(sf);
    const symbols=moduleSymbol?checker.getExportsOfModule(moduleSymbol):[];
    const result=new Map();
    for(const s of symbols)result.set(s.name,{symbol:s,runtime:runtimeExport(p,s.name)});
    exportMemo.set(p,result);return result;
  }
  function classMembers(real) {
    const declaration=real?.declarations?.find(ts.isClassDeclaration);if(!declaration)return null;
    const instance=checker.getDeclaredTypeOfSymbol(real), statics=checker.getTypeOfSymbolAtLocation(real,declaration);
    const list=(ty,side)=>checker.getPropertiesOfType(ty).filter(s=>s.name!=='prototype').flatMap(s=>{
      const ds=(s.declarations||[]).filter(d=>d.getSourceFile().fileName.startsWith(root+path.sep));
      if(!ds.length||ds.every(d=>modifiers(d).has(ts.SyntaxKind.PrivateKeyword)||modifiers(d).has(ts.SyntaxKind.ProtectedKeyword)||d.name&&ts.isPrivateIdentifier(d.name)))return [];
      const d=ds[0];return [{name:s.name,side,kind:ts.SyntaxKind[d.kind],inherited:d.parent!==declaration,
        declarations:ds.map(declarationInfo),callable:checker.getSignaturesOfType(checker.getTypeOfSymbolAtLocation(s,d),ts.SignatureKind.Call).length>0,
        parameters:parameters(ts.isPropertyDeclaration(d)&&d.initializer?unwrap(d.initializer):d),
        runtimeAssignmentOrigins:dynamicSites.filter(site=>site.source===rel(d.getSourceFile().fileName)&&site.lexicalClassStart===d.parent.getStart(d.getSourceFile())&&site.resolvedNames?.includes(s.name)&&site.expression.text.startsWith('this')).map(site=>({source:site.source,line:site.line,kind:site.kind,parameters:site.parameters||[],review:'lexical_this_assignment_requires_runtime_contract'})),
        initialization:ts.isPropertyDeclaration(d)&&!d.initializer?'declared_field_runtime_origin_requires_review':'source_declaration',evidence:evidence()}];
    }).sort((a,b)=>compare(a.name,b.name));
    const constructors=declaration.members.filter(ts.isConstructorDeclaration).map(d=>({...declarationInfo(d),parameters:parameters(d)}));
    return {constructors,instance:list(instance,'instance'),static:list(statics,'static'),lifecycleContract:'pending'};
  }
  function valueShape(ty) {
    let excludedHostOrIntrinsicMemberCount=0;
    const members=checker.getPropertiesOfType(ty).flatMap(s=>{
      const owned=(s.declarations||[]).filter(d=>d.getSourceFile().fileName.startsWith(root+path.sep));
      if(!owned.length){excludedHostOrIntrinsicMemberCount++;return [];}
      const ds=owned.filter(d=>!modifiers(d).has(ts.SyntaxKind.PrivateKeyword)&&!modifiers(d).has(ts.SyntaxKind.ProtectedKeyword)&&!(d.name&&ts.isPrivateIdentifier(d.name)));
      if(!ds.length)return [];
      const memberType=checker.getTypeOfSymbolAtLocation(s,ds[0]);
      const calls=checker.getSignaturesOfType(memberType,ts.SignatureKind.Call);
      return [{name:s.name,declarations:ds.map(declarationInfo),declaredType:brief(checker.typeToString(memberType)),
        callable:calls.length>0,signatures:calls.map(sig=>{const d=sig.declaration,owned=d&&d.getSourceFile().fileName.startsWith(root+path.sep);return {declarations:owned?[declarationInfo(d)]:[],parameters:owned?parameters(d):[],hostTypeAssumption:owned?null:'external_type_model_required',review:'type_derived_signature_requires_runtime_contract'};}),evidence:evidence()}];
    }).sort((a,b)=>compare(a.name,b.name));
    return {members,excludedHostOrIntrinsicMemberCount,hostOrIntrinsicMembersPresent:excludedHostOrIntrinsicMemberCount>0,
      hostTypeAssumption:excludedHostOrIntrinsicMemberCount?'external_type_model_required':null,
      review:'one_level_type_derived_candidates; nested, reflective and dynamic surface exhaustiveness remain open'};
  }
  const exports=exportEntries.map(entry=>{
    const symbols=[...exportPhases(entry.source)].map(([name,{symbol,runtime}])=>{
      const real=resolveSymbol(symbol); const declarations=(real?.declarations||[]).filter(d=>d.getSourceFile().fileName.startsWith(root+path.sep));
      const callable=declarations.filter(d=>d.parameters||ts.isVariableDeclaration(d)&&d.initializer&&(ts.isArrowFunction(unwrap(d.initializer))||ts.isFunctionExpression(unwrap(d.initializer))));
      const signatures=runtime&&declarations.length?checker.getSignaturesOfType(checker.getTypeOfSymbolAtLocation(real,declarations[0]),ts.SignatureKind.Call):[];
      const returnedShapes=signatures.map(sig=>{const ty=checker.getReturnTypeOfSignature(sig);return {declaredType:brief(checker.typeToString(ty)),members:checker.getPropertiesOfType(ty).flatMap(s=>{const ds=(s.declarations||[]).filter(d=>d.getSourceFile().fileName.startsWith(root+path.sep)&&!modifiers(d).has(ts.SyntaxKind.PrivateKeyword)&&!modifiers(d).has(ts.SyntaxKind.ProtectedKeyword)&&!(d.name&&ts.isPrivateIdentifier(d.name)));return ds.length?[{name:s.name,declarations:ds.map(declarationInfo),parameters:parameters(ds[0])}]:[];}).sort((a,b)=>compare(a.name,b.name)),review:'type_inferred_returned_surface_requires_runtime_contract'};});
      const publicClass=runtime?classMembers(real):null;
      return {name,classification:runtime?'runtime':'type_only',declarations:declarations.map(declarationInfo),
        signatures:callable.map(d=>parameters(ts.isVariableDeclaration(d)?unwrap(d.initializer):d)),returnedShapes,class:publicClass,
        valueShape:runtime&&!publicClass&&declarations.length?valueShape(checker.getTypeOfSymbolAtLocation(real,declarations[0])):null,
        contract:'not_specified',evidence:evidence()};
    }).sort((a,b)=>compare(a.name,b.name));
    return {...entry,classification:symbols.some(s=>s.classification==='runtime')?'runtime_or_mixed':'type_only',symbols};
  });
  const closure=start=>{const seen=new Set();const walk=p=>{if(seen.has(p))return;seen.add(p);for(const e of dependencies.get(p)||[])if(e.target)walk(e.target);};walk(start);return [...seen].sort();};
  for(const entry of exports)entry.conservativeSourceDependencies=closure(entry.source);
  // Index test imports and their transitive target dependencies, not filename guesses.
  const upstreamTests=[];
  for(const test of testFiles){
    const sf=ts.createSourceFile(test,fs.readFileSync(abs(test),'utf8'),ts.ScriptTarget.ES2022,true,test.endsWith('x')?ts.ScriptKind.TSX:ts.ScriptKind.TS);
    const targets=new Set(),imports=[];
    const visit=node=>{if((ts.isImportDeclaration(node)||ts.isExportDeclaration(node))&&node.moduleSpecifier&&ts.isStringLiteral(node.moduleSpecifier)){const found=resolve(node.moduleSpecifier.text,abs(test));const p=found&&rel(found.resolvedFileName);imports.push({specifier:node.moduleSpecifier.text,target:sourceSet.has(p)?p:null});if(sourceSet.has(p))for(const d of closure(p))targets.add(d);}ts.forEachChild(node,visit);};visit(sf);
    for(const p of targets)modules.get(p).upstreamTests.push(test);
    upstreamTests.push({source:test,sha256:hash(sf.text),imports,conservativeSourceDependencies:[...targets].sort(),assertionCoverage:'not_analyzed'});
  }
  const diagnostics=program.getSemanticDiagnostics().map(d=>({code:d.code,category:ts.DiagnosticCategory[d.category],source:d.file?rel(d.file.fileName):null,
    line:d.file&&d.start!==undefined?d.file.getLineAndCharacterOfPosition(d.start).line+1:null,message:ts.flattenDiagnosticMessageText(d.messageText,' ')})).sort((a,b)=>compare(JSON.stringify(a),JSON.stringify(b)));
  const reachable=new Set(exports.flatMap(e=>e.conservativeSourceDependencies));
  for(const module of modules.values()){module.reachableFromPublishedSource=reachable.has(module.source);module.upstreamTests.sort();if(!reachable.has(module.source))gaps.push({kind:'source_outside_conservative_export_closure',source:module.source,review:'not_a_proved_unreachability_result'});}
  if(diagnostics.length)gaps.push({kind:'semantic_analysis_incomplete',diagnosticCount:diagnostics.length,reason:'Hono dependencies/platform typings are intentionally not installed; source structure is indexed but type-derived shapes require review.'});
  const standardLibraryInputs=program.getSourceFiles().filter(sf=>program.isSourceFileDefaultLibrary(sf)).map(sf=>({name:path.basename(sf.fileName),sha256:hash(sf.text)})).sort((a,b)=>compare(a.name,b.name));
  return {exports,modules:[...modules.values()],dynamicSites,gaps,diagnostics,upstreamTests,standardLibraryInputs,
    summary:{expandedEntryPoints:exports.length,runtimeOrMixedEntryPoints:exports.filter(e=>e.classification!=='type_only').length,
      typeOnlyEntryPoints:exports.filter(e=>e.classification==='type_only').length,sourceModules:modules.size,
      runtimeOrMixedModules:[...modules.values()].filter(m=>m.classification!=='erased_type_only').length,
      erasedTypeOnlyModules:[...modules.values()].filter(m=>m.classification==='erased_type_only').length,
      exportSymbolOccurrences:exports.reduce((n,e)=>n+e.symbols.length,0),runtimeExportSymbolOccurrences:exports.reduce((n,e)=>n+e.symbols.filter(s=>s.classification==='runtime').length,0),
      exportedValueMemberOccurrences:exports.reduce((n,e)=>n+e.symbols.reduce((m,s)=>m+(s.valueShape?.members.length||0),0),0),
      sourceDeclarations:[...modules.values()].reduce((n,m)=>n+m.declarations.length,0),dynamicSites:dynamicSites.length,upstreamTestFiles:testFiles.length,
      semanticDiagnostics:diagnostics.length,sourceConnectedTheorems:0}};
}

export function generate(root, target, parser) {
  const files=verifyCheckout(root,target);
  const pkg=JSON.parse(fs.readFileSync(path.join(root,'package.json'),'utf8'));
  const entries=expandExports(pkg.exports,files);
  const scan=scanProject(root,files,parser.ts,entries);
  const declarations=new Map();
  const declarationKeys=['source','line','start','end','kind','name','sha256'];
  function normalize(value){
    if(Array.isArray(value))return value.map(normalize);
    if(!value||typeof value!=='object')return value;
    if(declarationKeys.every(k=>Object.hasOwn(value,k))){
      const id=`${value.source}:${value.start}-${value.end}:${value.kind}`;
      declarations.set(id,{id,...Object.fromEntries(declarationKeys.map(k=>[k,value[k]]))});
      const extras=Object.fromEntries(Object.entries(value).filter(([k])=>!declarationKeys.includes(k)).map(([k,v])=>[k,normalize(v)]));
      return Object.keys(extras).length?{declarationId:id,...extras}:id;
    }
    return Object.fromEntries(Object.entries(value).map(([k,v])=>[k,normalize(v)]));
  }
  const normalized=normalize(scan);
  normalized.summary.uniqueDeclarations=declarations.size;
  return {schemaVersion:1,target:{repository:target.repository,revision:target.revision,package:pkg.name,declaredVersion:pkg.version,
      packageJsonSha256:hash(fs.readFileSync(path.join(root,'package.json')))},
    scanner:{file:'verification/inventory.mjs',sha256:hash(fs.readFileSync(fileURLToPath(import.meta.url))),parser:parser.metadata,
      status:'unverified_structural_inventory_tool',sourceMapping:'dist/*.js → src/*.ts or *.tsx; expanded wildcard subpaths including slashes',
      dependencyReachability:'conservative module closure includes erased imports; no path-sensitive runtime reachability proof',
      testMapping:'syntactic upstream test imports and transitive module dependencies; not assertion/property coverage',
      classShape:'TypeScript checker public own/inherited members plus computed/reflective/proxy sites; unmodeled behavior remains pending',
      exportedValueShape:'One-level type-derived source-owned member candidates on runtime non-class exports; nested/reflective/dynamic exhaustiveness remains open',
      declarationOffsets:'UTF-16 code-unit offsets used by the TypeScript parser; SHA256 hashes bind UTF-8 source text'},
    coverageStatus:'structural_inventory_only; contracts, dynamic API review and source connections remain open',
    ...normalized,declarationEvidenceDefault:evidence(),declarations:[...declarations.values()].sort((a,b)=>compare(a.id,b.id))};
}

export function writeOrCheck(output,result,check){
  const text=JSON.stringify(result,null,2)+'\n';
  if(check){if(!fs.existsSync(output)||fs.readFileSync(output,'utf8')!==text)throw new Error(`Coverage ledger stale: regenerate ${output}`);}
  else fs.writeFileSync(output,text);
}

function main(){
  const args=process.argv.slice(2);let source=path.resolve(HERE,'../../hono'),output=path.join(HERE,'coverage.json'),typescript,check=false;
  for(let i=0;i<args.length;i++){if(args[i]==='--hono')source=path.resolve(args[++i]);else if(args[i]==='--typescript')typescript=args[++i];else if(args[i]==='--output')output=path.resolve(args[++i]);else if(args[i]==='--check')check=true;else throw new Error(`Unknown argument ${args[i]}`);}
  const target=JSON.parse(fs.readFileSync(path.join(HERE,'target.json'),'utf8'));
  const result=generate(source,target,loadTypeScript(typescript));writeOrCheck(output,result,check);
  console.log(JSON.stringify({mode:check?'checked':'generated',...result.summary,coverageStatus:result.coverageStatus},null,2));
}
if(process.argv[1]&&pathToFileURL(path.resolve(process.argv[1])).href===import.meta.url){try{main();}catch(error){console.error(error.message);process.exitCode=1;}}
