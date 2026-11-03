# Selected weight unit columns

Proposed `elvWeightUnit_dotPower_comparison` identifies the selected weight unit followed by every ordinary power of the selected upper dot component with the ordinary content unit/dot column, through the selected successor-coordinate equality. It applies at every output block, without requiring that block to have a lower predecessor. This is a supporting comparison for BE (1.14).

The producer and paired concrete consumer are proposed and not yet jointly checked. The consumer includes both moving parities, empty and singleton output contents, arbitrary dot powers and parity-shifted truncated ELV representables. Relating the powers to the selected `SKM.rouquierPower` fields and using a constructed finite matrix inverse are separate obligations.
