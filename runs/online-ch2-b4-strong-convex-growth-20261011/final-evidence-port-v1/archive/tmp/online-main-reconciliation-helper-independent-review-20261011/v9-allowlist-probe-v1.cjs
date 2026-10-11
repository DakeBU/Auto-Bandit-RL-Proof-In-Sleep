const mathjaxStartup='https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js'; const mathjaxFontPrefix='https://cdn.jsdelivr.net/npm/mathjax@3/es5/output/chtml/fonts/woff-v2/';
  function allowedMathjax(target) {
    const x=new URL(target);
    if(x.protocol!=='https:'||x.origin!=='https://cdn.jsdelivr.net'||x.search||x.hash||x.username||x.password)return false;
    return x.href===mathjaxStartup||(x.href.startsWith(mathjaxFontPrefix)&&/^MathJax_[A-Za-z0-9_-]+\.woff$/.test(x.href.slice(mathjaxFontPrefix.length)));
  }

const cases=[
[mathjaxStartup,true],
[mathjaxFontPrefix+'MathJax_Main-Regular.woff',true],
[mathjaxFontPrefix+'MathJax_Math-Italic.woff',true],
['https://cdn.jsdelivr.net/npm/mathjax@3/es5/input/tex/extensions/ams.js',false],
['https://cdn.jsdelivr.net/npm/mermaid@11.4.1/dist/mermaid.esm.min.mjs',false],
[mathjaxStartup+'?x=1',false],
[mathjaxStartup+'#x',false],
['https://user@cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js',false],
[mathjaxFontPrefix+'../tex-chtml.js',false],
[mathjaxFontPrefix+'%2e%2e/tex-chtml.js',false],
[mathjaxFontPrefix+'other.woff',false],
[mathjaxFontPrefix+'MathJax_Main-Regular.woff2',false],
['https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml.js',false],
['http://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js',false]];
for(const [url,expected] of cases)if(allowedMathjax(url)!==expected)throw Error('Unexpected allowlist result '+url);
console.log(JSON.stringify({cases:cases.length,passed:true,scope:'extracted exact URL predicate; no network/browser'}));
