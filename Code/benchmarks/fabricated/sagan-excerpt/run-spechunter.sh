#!/bin/zsh

~/Taint-Analysis/Code/infer/infer/bin/infer spechunter
dot -Tsvg callgraph_with_astate_refined.dot -o callgraph_with_astate_refined.svg
