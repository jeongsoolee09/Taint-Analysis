#!/bin/zsh

# Automates the process right before running loop or self_question_n_answer

echo "[1/10] Creating CPT_lookup_table..."
python make_CPT_lookup_table.py
echo "\n"

echo "[2/10] Creating nodes..."
python create_node.py
echo "\n"

echo "[3/10] Creating df and call edges..."
python create_edge.py
echo "\n"

echo "[4/10] Computing pairwise similarity..."
python pairwise_similarity.py
echo "\n"

echo "[5/10] Extracting extra features..."
python extra_features.py
echo "\n"

echo "[6/10] Making underlying graph..."
python make_underlying_graph.py
echo "\n"

echo "[7/10] Splitting underlying graph..."
python split_underlying_graph.py
echo "\n"

echo "[8/10] Redistributing and reconnecting completely isolated nodes..."
python reconnect_poor_nodes.py
echo "\n"

echo "[9/10] Reconnecting small isolated groups..."
python reconnect_small_groups.py
echo "\n"

echo "[10/10] Running graph contraction..."
python graph_contraction.py
echo "\n"

echo "All preprocessing done! Now either run loop.py or self_question_n_answer.py."
