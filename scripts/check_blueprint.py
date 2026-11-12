#!/usr/bin/env python3
"""Validate the mathematical blueprint's source identity, anchors, and web links."""
from pathlib import Path
import argparse,hashlib,html,json,re,xml.etree.ElementTree as ET
from urllib.parse import unquote,urlsplit
ROOT=Path(__file__).resolve().parents[1]
BP=ROOT/'blueprint'
def check(rendered=False):
    receipt=json.loads((BP/'proof-source-manifest.json').read_text(encoding='utf-8'))
    for name,digest in receipt['sha256'].items():
        path=ROOT/name
        assert path.is_file(),f'Missing proof input: {name}'
        assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,f'Proof input changed: {name}; review and refresh blueprint evidence'
    assert {str(p.relative_to(ROOT)).replace('\\','/') for p in (ROOT/'Proofs').glob('*.lean')}=={p for p in receipt['sha256'] if p.endswith('.lean')}
    nodes=json.loads((BP/'nodes.json').read_text(encoding='utf-8'))
    ids={n['id'] for n in nodes};assert len(ids)==len(nodes),'Duplicate graph labels'
    declarations={}
    for n in nodes:
        assert set(n['dependencies'])<=ids,f'Unknown dependency in {n["id"]}'
        for d in n['declarations']:
            line=(ROOT/d['file']).read_text(encoding='utf-8-sig').splitlines()[d['line']-1]
            short=re.escape(d['name'].split('.')[-1])
            assert re.match(r'^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure)\s+'+short+r'\b',line),f'Stale declaration anchor: {d}'
            declarations[d['name']]=d['file']+'#L'+str(d['line'])
    visiting=set();visited=set();by_id={n['id']:n for n in nodes}
    def visit(id):
        assert id not in visiting,f'Cyclic mathematical dependencies at {id}'
        if id in visited:return
        visiting.add(id)
        for dep in by_id[id]['dependencies']:visit(dep)
        visiting.remove(id);visited.add(id)
    for id in ids:visit(id)
    links=dict(line.split('\t') for line in (BP/'src/source-links.tsv').read_text(encoding='utf-8').splitlines())
    assert links==declarations,'Source-link registry differs from node declarations'
    content=(BP/'src/content.tex').read_text(encoding='utf-8')
    assert set(re.findall(r'\\label\{([^}]+)\}',content))==ids,'TeX node labels differ from graph registry'
    used=set(x.strip() for group in re.findall(r'\\uses\{([^}]+)\}',content) for x in group.split(','))
    assert used<=ids,'Unresolved dependency in TeX'
    tex_decls=set(x.strip() for group in re.findall(r'\\lean\{([^}]+)\}',content) for x in group.split(','))
    assert tex_decls==set(declarations),'TeX declaration list differs from source registry'
    if rendered:
        web=BP/'web';assert (web/'index.html').is_file(),'Missing web entry point'
        pages=list(web.glob('*.html'));assert pages,'No rendered pages'
        all_html=html.unescape('\n'.join(p.read_text(encoding='utf-8') for p in pages))
        base='https://github.com/daviddhilbert/ACVF-QE/blob/'+receipt['proof_revision']+'/'
        for name,loc in links.items():assert base+loc in all_html,f'Missing rendered Lean link: {name}'
        svg=ET.parse(web/'dependency-graph.svg').getroot()
        graph_nodes=[e for e in svg.iter() if e.tag.endswith('}g') and e.attrib.get('class')=='node']
        assert len(graph_nodes)==len(nodes),f'Expected {len(nodes)} clickable graph nodes; got {len(graph_nodes)}'
        for n in graph_nodes:
            anchors=[a for a in n.iter() if a.tag.endswith('}a')]
            assert anchors,'Unlinked SVG node'
            for a in anchors:
                href=a.attrib.get('{http://www.w3.org/1999/xlink}href',a.attrib.get('href',''))
                u=urlsplit(href);assert not u.scheme,'Unexpected external statement link'
                target=web/unquote(u.path)
                assert target.is_file(),f'Missing graph target: {href}'
                page=target.read_text(encoding='utf-8')
                if u.fragment:assert re.search(r'(?:id|name)=[\"\']'+re.escape(unquote(u.fragment))+r'[\"\']',page),f'Missing statement anchor: {href}'
    print(json.dumps({'nodes':len(nodes),'declarations':len(declarations),'proof_inputs':len(receipt['sha256']),'rendered':rendered,'status':'PASS'}))
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--rendered',action='store_true')
    check(parser.parse_args().rendered)
