#!/bin/zsh

# Automates the process right before running loop or self_question_n_answer

echo "creating CPT_lookup_table..."
python make_CPT_lookup_table.py
echo "\n"

echo "creating nodes..."
python create_node.py
echo "\n"

echo "creating df and call edges..."
python create_edge.py
echo "\n"

echo "computing pairwise similarity..."
python pairwise_similarity.py
echo "\n"

echo "extracting extra features..."
python extra_features.py
echo "\n"


echo "making underlying graph..."
python make_underlying_graph.py
echo "\n"

echo "splitting underlying graph..."
python split_underlying_graph.py
echo "\n"

echo "reconnecting possibly missing edges..."
python reconnect_poor_nodes.py
echo "\n"

echo "Done! Now either run loop.py or self_question_n_answer.py."
