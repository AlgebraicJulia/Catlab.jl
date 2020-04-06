#!/usr/bin/env bash

dot simple_digraph.dot -Tjson0 > simple_digraph.json
neato simple_graph.dot -Tjson0 > simple_graph.json
