#!/usr/bin/env node
// Execute the shipped widget JavaScript against a minimal DOM test double.
// This checks interaction logic, not browser layout, CSS, or accessibility.
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),assert=require('node:assert/strict');
class Element {
  constructor(tag='div'){this.tag=tag;this.children=[];this.value='';this.checked=false;this.textContent='';this.className='';}
  append(...elements){this.children.push(...elements);}
  replaceChildren(...elements){this.children=[...elements];}
  insertRow(){const e=new Element('tr');this.append(e);return e;}
  insertCell(){const e=new Element('td');this.append(e);return e;}
  addEventListener(){}
}
function all(node,tag){return [...(node.tag===tag?[node]:[]),...node.children.flatMap(e=>all(e,tag))];}
const root=path.join(__dirname,'..','examples');let comparisons=0;
for(const file of fs.readdirSync(root).filter(x=>/^[BP]\d\d\.html$/.test(x))){
  const html=fs.readFileSync(path.join(root,file),'utf8');
  const data=html.match(/<script id="profile-data" type="application\/json">([\s\S]*?)<\/script>/)[1];
  const script=html.match(/<script>\s*([\s\S]*?)<\/script>/)[1];
  const elements={};for(const id of ['profile-data','axis-x','axis-y','bridge','closure','slices'])elements[id]=new Element();
  elements['profile-data'].textContent=data;elements['axis-x'].value='0';elements['axis-y'].value='2';
  const document={getElementById:id=>elements[id],createElement:tag=>new Element(tag)};
  const context=vm.createContext({document,console});vm.runInContext(script,context);
  const cells=()=>all(elements.slices,'td');
  assert.equal(cells().length,16);assert(cells().every(c=>c.className==='unknown'));
  elements.bridge.checked=true;vm.runInContext('renderSlices()',context);
  if(file==='B01.html')assert.equal(cells().filter(c=>c.className==='empirical').length,2);
  if(file==='B02.html')assert.equal(cells().filter(c=>c.className==='empirical').length,0);
  elements.closure.checked=true;vm.runInContext('renderSlices()',context);
  assert.equal(cells().filter(c=>c.className==='formal').length,4);
  for(let x=0;x<4;x++)for(let y=0;y<4;y++){
    if(x===y)continue;
    elements['axis-x'].value=String(x);elements['axis-y'].value=String(y);
    vm.runInContext('renderSlices()',context);
    assert.equal(elements.slices.children.length,4);assert.equal(cells().length,16);comparisons++;
  }
  elements['axis-x'].value='1';elements['axis-y'].value='1';
  vm.runInContext('renderSlices(xSelect)',context);
  assert.notEqual(elements['axis-x'].value,elements['axis-y'].value);
  assert.equal(cells().length,16);
}
assert.equal(comparisons,14*12);
console.log('HTML widget logic passed: 14 pages, 168 axis selections, safe default evidence state. Browser layout not tested.');
