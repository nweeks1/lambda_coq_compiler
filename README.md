# lambda_coq_compiler

Compilateur des lambdas termes vers les machine de krivine écrit en coq avec quelques théorèmes sur la compilation.

Les définitions importantes sont dans definitions.v, des lemmes inutiles (presque que des inégalités qui se prouvent avec lia) se trouvent dans lemmas.v,
tandis que toutes les preuves des théorèmes se trouvent dans project.v.

Pour lire le code, je conseille de lancer "make html" puis ouvrir les fichiers qui se trouvent dans le dossier html, j'ai ajouté des commentaires au dessus de chaque lemme/théorème pour que tout soit compréhensible.
En revanche, les preuves des théorèmes sont assez indigestes (j'ai appris coq grâce à ce projet et j'ai clairement pas des bonnes pratiques, avec du recul, j'aurai du donner des noms aux hypothèses variables, au lieu de tout faire en m'aidant de l'ide, c'est certes une méthode efficace mais c'est impossible à relire).
