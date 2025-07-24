# Recreds
A proof of concept implemention of Re2creds: Reusable Anonymous Credential Scheme based on Recursive SNARKs.

Re2creds is the first reusable anonymous credential scheme with expressive functionality and high performance. Primarily, our design features a malleable SNARK system utilizing recursive composition, hence surpassing existing schemes in expressiveness, offering not just simple rerandomization but also predicate updates, credential
aggregation, and issuer hiding capabilities. Furthermore, we innovatively propose a proof of possession mechanism for signatures that strategically offloads complex verification computations outside the SNARK circuit. This approach substantially reduces proof costs by requiring only proof of knowledge with respect to the credentials.
