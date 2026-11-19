"""Resolve blueprint declarations to the checked ACVF-QE source revision."""
from pathlib import Path
import json
SOURCE = "https://github.com/daviddhilbert/ACVF-QE/blob/" + json.loads(
    Path(__file__).resolve().parents[1].joinpath("proof-source-manifest.json").read_text(encoding="utf-8"))["proof_revision"] + "/"
def ProcessOptions(options, document):
    links = dict(line.split("\t") for line in Path(__file__).with_name("source-links.tsv").read_text(encoding="utf-8").splitlines())
    def set_source_links():
        for graph in document.userdata["dep_graph"]["graphs"].values():
            for node in graph.nodes:
                node.userdata["lean_urls"] = [(name, links[name] if links[name].startswith("https://") else SOURCE + links[name]) for name in node.userdata.get("leandecls", [])]
    document.addPostParseCallbacks(160, set_source_links)
