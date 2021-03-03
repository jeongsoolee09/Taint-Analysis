#!/bin/zsh

# Automates the process right before running loop or self_question_n_answer

echo "creating nodes.."
python create_node.py

echo "extracting features.."
python feature_extract.py

echo "creating edges.."
python create_edge.py

echo "making underlying graph.."
python make_underlying_graph.py

echo "splitting underlying graph.."
python split_underlying_graph.py

echo "Done! Now either run loop.py or self_question_n_answer.py."
