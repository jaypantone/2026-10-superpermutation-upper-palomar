module

public import upper.certificate.Checks

@[expose] public section

/-! Preserved omitted-loop strings. Every permutation check decodes at most32 strings. -/
namespace SuperpermutationUpperBound.Native14.Certificate.EmptyLoopParts.BlockF01
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List String := [
  "01A28374569",
  "01A28394756",
  "01A28739456",
  "01A28793456",
  "01A28973456",
  "01A29345867",
  "01A29347568",
  "01A29347586",
  "01A29348567",
  "01A29374586",
  "01A29384576",
  "01A29387456",
  "01A29873456",
  "01A72345968",
  "01A72349568",
  "01A72384956",
  "01A72893456",
  "01A72934568",
  "01A72983456",
  "01A78293456",
  "01A82345967",
  "01A82374569",
  "01A82374956",
  "01A82934567",
  "01A82937456",
  "01A87293456",
  "01A92345768",
  "01A92347568",
  "01A92348567",
  "01A92348576",
  "01A92374586",
  "01A92374856"
]

theorem length00 : encoded00.length = 32 := by rfl

def bases00 : List (List Nat) := encoded00.map (fun x => x.toList.map decodeLetter)

theorem checked00 : bases00.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded01 : List String := [
  "01A92384576",
  "01A92734856",
  "01A92834756",
  "01A92873456",
  "0712345869A",
  "071234586A9",
  "07123458A69",
  "0712345A869",
  "0712349586A",
  "071234958A6",
  "07123495A86",
  "0712349A586",
  "071234A5869",
  "071234A9586",
  "0712394586A",
  "071239458A6",
  "07123945A68",
  "07123945A86",
  "0712394A568",
  "0712394A586",
  "071239A4568",
  "071239A4586",
  "07123A45869",
  "07123A49586",
  "07123A94568",
  "07123A94586",
  "0712834569A",
  "071283456A9",
  "0712834596A",
  "071283459A6",
  "07128345A69",
  "07128345A96"
]

theorem length01 : encoded01.length = 32 := by rfl

def bases01 : List (List Nat) := encoded01.map (fun x => x.toList.map decodeLetter)

theorem checked01 : bases01.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded02 : List String := [
  "0712834956A",
  "071283495A6",
  "07128349A56",
  "0712834A569",
  "0712834A596",
  "0712834A956",
  "0712839456A",
  "071283945A6",
  "07128394A56",
  "0712839A456",
  "071283A4569",
  "071283A4596",
  "071283A4956",
  "071283A9456",
  "07128A34569",
  "07128A39456",
  "0712934A586",
  "071293A4586",
  "07129A34586",
  "0712A345869",
  "0712A349586",
  "0712A394568",
  "0712A394586",
  "0712A834569",
  "0712A839456",
  "0712A934586",
  "0718234596A",
  "071823459A6",
  "07182345A96",
  "0718234A596",
  "071823945A6",
  "07182394A56"
]

theorem length02 : encoded02.length = 32 := by rfl

def bases02 : List (List Nat) := encoded02.map (fun x => x.toList.map decodeLetter)

theorem checked02 : bases02.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded03 : List String := [
  "0718239A456",
  "071823A4596",
  "071823A9456",
  "07182A39456",
  "0719234586A",
  "071923458A6",
  "07192345A86",
  "0719234A586",
  "071923A4586",
  "07192A34586",
  "0719A234586",
  "071A2345869",
  "071A2349586",
  "071A2394586",
  "071A2834569",
  "071A2839456",
  "071A2934586",
  "071A9234586",
  "071A9823456",
  "078A1234569",
  "07918A23456",
  "0791A823456",
  "079A1823456",
  "07A12345869",
  "07A12349586",
  "07A12394586",
  "07A12834569",
  "07A12839456",
  "07A19234586",
  "07A19823456",
  "0812345679A",
  "0812349576A"
]

theorem length03 : encoded03.length = 32 := by rfl

def bases03 : List (List Nat) := encoded03.map (fun x => x.toList.map decodeLetter)

theorem checked03 : bases03.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded04 : List String := [
  "081234957A6",
  "08123495A67",
  "08123495A76",
  "0812349A567",
  "0812349A576",
  "081234A9567",
  "081234A9576",
  "0812394A576",
  "081239A4576",
  "08123A49567",
  "08123A49576",
  "08123A94576",
  "0812734569A",
  "081273456A9",
  "0812734596A",
  "081273459A6",
  "08127345A69",
  "08127345A96",
  "0812734956A",
  "081273495A6",
  "08127349A56",
  "0812734A569",
  "0812734A596",
  "0812734A956",
  "0812739456A",
  "081273945A6",
  "08127394A56",
  "0812739A456",
  "081273A4569",
  "081273A4596",
  "081273A4956",
  "081273A9456"
]

theorem length04 : encoded04.length = 32 := by rfl

def bases04 : List (List Nat) := encoded04.map (fun x => x.toList.map decodeLetter)

theorem checked04 : bases04.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded05 : List String := [
  "08127A34569",
  "08127A34596",
  "08127A39456",
  "0812934A567",
  "0812934A576",
  "081293A4567",
  "081293A4576",
  "08129A34567",
  "08129A34576",
  "0812A349567",
  "0812A349576",
  "0812A394576",
  "0812A734569",
  "0812A734596",
  "0812A739456",
  "0812A934567",
  "0812A934576",
  "0817234956A",
  "081723495A6",
  "08172349A56",
  "0817234A956",
  "081723A4956",
  "0819234576A",
  "081923457A6",
  "08192345A76",
  "0819234A576",
  "081923A4576",
  "0819273456A",
  "081927345A6",
  "08192734A56",
  "0819273A456",
  "081927A3456"
]

theorem length05 : encoded05.length = 32 := by rfl

def bases05 : List (List Nat) := encoded05.map (fun x => x.toList.map decodeLetter)

theorem checked05 : bases05.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded06 : List String := [
  "08192A34576",
  "08192A73456",
  "0819A234576",
  "0819A273456",
  "081A2349576",
  "081A2394576",
  "081A2734569",
  "081A2734596",
  "081A2739456",
  "081A2934567",
  "081A2934576",
  "081A9234576",
  "081A9273456",
  "0871234569A",
  "087123456A9",
  "08712345A69",
  "0871234A569",
  "087123A4569",
  "08712A34569",
  "0871923456A",
  "087192345A6",
  "08719234A56",
  "0871923A456",
  "087192A3456",
  "08719A23456",
  "0871A234569",
  "0871A923456",
  "0879123456A",
  "087912345A6",
  "08791234A56",
  "0879123A456",
  "087912A3456"
]

theorem length06 : encoded06.length = 32 := by rfl

def bases06 : List (List Nat) := encoded06.map (fun x => x.toList.map decodeLetter)

theorem checked06 : bases06.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded07 : List String := [
  "08791A23456",
  "087A1234569",
  "087A1923456",
  "089123456A7",
  "0897123456A",
  "089712345A6",
  "08971234A56",
  "0897123A456",
  "089712A3456",
  "08971A23456",
  "08A12345679",
  "08A12345697",
  "08A12349576",
  "08A12734569",
  "08A12734596",
  "08A12739456",
  "08A19234576",
  "08A19273456",
  "08A71234569",
  "08A71923456",
  "0912345687A",
  "091234568A7",
  "09123456A78",
  "09123456A87",
  "0912345A687",
  "0912347568A",
  "091234756A8",
  "0912347586A",
  "09123475A68",
  "0912347A568",
  "0912348567A",
  "091234856A7"
]

theorem length07 : encoded07.length = 32 := by rfl

def bases07 : List (List Nat) := encoded07.map (fun x => x.toList.map decodeLetter)

theorem checked07 : bases07.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded08 : List String := [
  "09123485A67",
  "0912348A567",
  "091234A5687",
  "091234A7568",
  "091234A8567",
  "0912374586A",
  "0912384576A",
  "0912384756A",
  "09123A45687",
  "09123A47568",
  "09123A48567",
  "0912734856A",
  "091273485A6",
  "0912738456A",
  "091273845A6",
  "0912834756A",
  "091283475A6",
  "09128347A56",
  "0912834A756",
  "091283A4756",
  "09128A34756",
  "0912A345687",
  "0912A347568",
  "0912A347586",
  "0912A348567",
  "0912A374586",
  "0912A384576",
  "0912A384756",
  "0912A834756",
  "0917234568A",
  "091723456A8",
  "09172345A68"
]

theorem length08 : encoded08.length = 32 := by rfl

def bases08 : List (List Nat) := encoded08.map (fun x => x.toList.map decodeLetter)

theorem checked08 : bases08.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded09 : List String := [
  "0917234A568",
  "0917238456A",
  "091723845A6",
  "09172384A56",
  "0917238A456",
  "091723A4568",
  "091723A8456",
  "09172A34568",
  "09172A38456",
  "09178A23456",
  "0917A234568",
  "0917A238456",
  "0918237456A",
  "091823745A6",
  "09182374A56",
  "0918237A456",
  "091823A7456",
  "09182A37456",
  "0918723456A",
  "091872345A6",
  "09187234A56",
  "0918723A456",
  "091872A3456",
  "09187A23456",
  "0918A237456",
  "0918A723456",
  "091A2345687",
  "091A2347568",
  "091A2347586",
  "091A2348567",
  "091A2374586",
  "091A2384576"
]

theorem length09 : encoded09.length = 32 := by rfl

def bases09 : List (List Nat) := encoded09.map (fun x => x.toList.map decodeLetter)

theorem checked09 : bases09.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded10 : List String := [
  "091A2384756",
  "091A2734856",
  "091A2738456",
  "091A2834756",
  "091A7234568",
  "091A7238456",
  "091A8237456",
  "091A8723456",
  "09718A23456",
  "0981234567A",
  "098123456A7",
  "0987123456A",
  "098712345A6",
  "09871234A56",
  "0987123A456",
  "098712A3456",
  "09871A23456",
  "09A12345687",
  "09A12347568",
  "09A12347586",
  "09A12348567",
  "09A12374586",
  "09A12384576",
  "09A12384756",
  "09A12734856",
  "09A12738456",
  "09A12834756",
  "09A17234568",
  "09A17238456",
  "09A18237456",
  "09A18723456",
  "0A123456879"
]

theorem length10 : encoded10.length = 32 := by rfl

def bases10 : List (List Nat) := encoded10.map (fun x => x.toList.map decodeLetter)

theorem checked10 : bases10.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded11 : List String := [
  "0A123456897",
  "0A123456987",
  "0A123458769",
  "0A123458796",
  "0A123458976",
  "0A123459687",
  "0A123459876",
  "0A123485967",
  "0A123487596",
  "0A123487956",
  "0A123489756",
  "0A123495876",
  "0A123498756",
  "0A123745869",
  "0A123748569",
  "0A123845769",
  "0A123849576",
  "0A123874956",
  "0A123879456",
  "0A123897456",
  "0A123947568",
  "0A123948567",
  "0A123948756",
  "0A123987456",
  "0A127348569",
  "0A127348596",
  "0A127384596",
  "0A128347569",
  "0A128347596",
  "0A128374569",
  "0A128394756",
  "0A128739456"
]

theorem length11 : encoded11.length = 32 := by rfl

def bases11 : List (List Nat) := encoded11.map (fun x => x.toList.map decodeLetter)

theorem checked11 : bases11.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded12 : List String := [
  "0A128793456",
  "0A128973456",
  "0A129347568",
  "0A129347586",
  "0A129348567",
  "0A129374586",
  "0A129384576",
  "0A129387456",
  "0A129873456",
  "0A172345968",
  "0A172349568",
  "0A172384569",
  "0A172384596",
  "0A172384956",
  "0A172834569",
  "0A172934568",
  "0A182345967",
  "0A182374569",
  "0A182374596",
  "0A182374956",
  "0A182734596",
  "0A182934567",
  "0A182937456",
  "0A187293456",
  "0A187923456",
  "0A189723456",
  "0A192345768",
  "0A192347568",
  "0A192348567",
  "0A192348576",
  "0A192374586",
  "0A192374856"
]

theorem length12 : encoded12.length = 32 := by rfl

def bases12 : List (List Nat) := encoded12.map (fun x => x.toList.map decodeLetter)

theorem checked12 : bases12.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded13 : List String := [
  "0A192384576",
  "0A192734856",
  "0A192834756",
  "0A192873456",
  "0A198723456",
  "0A712345869",
  "0A712349586",
  "0A712394586",
  "0A712834569",
  "0A712839456",
  "0A718923456",
  "0A719234586",
  "0A719823456",
  "0A781923456",
  "0A812345679",
  "0A812349576",
  "0A812734569",
  "0A812734596",
  "0A812739456",
  "0A819234576",
  "0A819273456",
  "0A871234569",
  "0A871923456",
  "0A912345687",
  "0A912347568",
  "0A912347586",
  "0A912348567",
  "0A912374586",
  "0A912384576",
  "0A912384756",
  "0A912734856",
  "0A912738456"
]

theorem length13 : encoded13.length = 32 := by rfl

def bases13 : List (List Nat) := encoded13.map (fun x => x.toList.map decodeLetter)

theorem checked13 : bases13.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded14 : List String := [
  "0A912834756",
  "0A917234568",
  "0A917238456",
  "0A918237456",
  "0A918723456",
  "0A981234567"
]

theorem length14 : encoded14.length = 6 := by rfl

def bases14 : List (List Nat) := encoded14.map (fun x => x.toList.map decodeLetter)

theorem checked14 : bases14.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded : List String :=
  encoded00 ++
  encoded01 ++
  encoded02 ++
  encoded03 ++
  encoded04 ++
  encoded05 ++
  encoded06 ++
  encoded07 ++
  encoded08 ++
  encoded09 ++
  encoded10 ++
  encoded11 ++
  encoded12 ++
  encoded13 ++
  encoded14

theorem encoded_length : encoded.length = 454 := by
  simp only [encoded, List.length_append, length00, length01, length02, length03, length04, length05, length06, length07, length08, length09, length10, length11, length12, length13, length14, Nat.reduceAdd]

def bases : List (List Nat) := encoded.map (fun x => x.toList.map decodeLetter)

theorem bases_blocks : bases =
  bases00 ++
  bases01 ++
  bases02 ++
  bases03 ++
  bases04 ++
  bases05 ++
  bases06 ++
  bases07 ++
  bases08 ++
  bases09 ++
  bases10 ++
  bases11 ++
  bases12 ++
  bases13 ++
  bases14 := by
  simp only [bases, encoded, List.map_append, bases00, bases01, bases02, bases03, bases04, bases05, bases06, bases07, bases08, bases09, bases10, bases11, bases12, bases13, bases14]

theorem bases_length : bases.length = 454 := by
  rw [bases, List.length_map]
  exact encoded_length

theorem checked : bases.all (fun x => decide (x.Perm (List.range 11))) = true := by
  simp only [bases_blocks, List.all_append, checked00, checked01, checked02, checked03, checked04, checked05, checked06, checked07, checked08, checked09, checked10, checked11, checked12, checked13, checked14, Bool.and_self]

end SuperpermutationUpperBound.Native14.Certificate.EmptyLoopParts.BlockF01
