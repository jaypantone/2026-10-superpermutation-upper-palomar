module

public import upper.certificate.Checks

@[expose] public section

/-! Preserved omitted-loop strings. Every permutation check decodes at most32 strings. -/
namespace SuperpermutationUpperBound.Native14.Certificate.EmptyLoopParts.BlockF00
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List String := [
  "01234576A98",
  "0123457968A",
  "012345796A8",
  "01234579A68",
  "0123457A698",
  "0123458769A",
  "012345876A9",
  "0123458796A",
  "01234587A69",
  "0123458976A",
  "0123458A769",
  "0123459678A",
  "0123459687A",
  "012345968A7",
  "01234596A87",
  "0123459768A",
  "0123459876A",
  "0123459A687",
  "012345A6879",
  "012345A6897",
  "012345A6987",
  "012345A7689",
  "012345A7698",
  "012345A7869",
  "012345A8769",
  "012345A9687",
  "0123475A986",
  "012347958A6",
  "01234795A86",
  "0123479A586",
  "012347A5986",
  "0123485967A"
]

theorem length00 : encoded00.length = 32 := by rfl

def bases00 : List (List Nat) := encoded00.map (fun x => x.toList.map decodeLetter)

theorem checked00 : bases00.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded01 : List String := [
  "012348596A7",
  "01234859A67",
  "0123485A967",
  "0123487596A",
  "012348759A6",
  "01234875A96",
  "0123487956A",
  "012348795A6",
  "0123487A596",
  "0123489756A",
  "012348975A6",
  "012348A5967",
  "012348A7596",
  "012349578A6",
  "0123495876A",
  "012349587A6",
  "01234958A76",
  "0123495A876",
  "012349758A6",
  "0123498756A",
  "012349875A6",
  "012349A5876",
  "01234A56879",
  "01234A56897",
  "01234A56987",
  "01234A58769",
  "01234A58796",
  "01234A58976",
  "01234A59687",
  "01234A59876",
  "01234A75896",
  "01234A75986"
]

theorem length01 : encoded01.length = 32 := by rfl

def bases01 : List (List Nat) := encoded01.map (fun x => x.toList.map decodeLetter)

theorem checked01 : bases01.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded02 : List String := [
  "01234A78596",
  "01234A85967",
  "01234A87596",
  "01234A95876",
  "0123745869A",
  "012374586A9",
  "01237458A69",
  "0123745A869",
  "0123748569A",
  "012374856A9",
  "01237485A69",
  "012374A5869",
  "012374A9856",
  "01237948A56",
  "0123794A856",
  "012379A4856",
  "01237A45869",
  "01237A49856",
  "0123845769A",
  "012384576A9",
  "01238457A69",
  "0123845A769",
  "0123849576A",
  "012384957A6",
  "01238495A76",
  "0123849A576",
  "012384A5769",
  "012384A9576",
  "0123874956A",
  "012387495A6",
  "01238749A56",
  "0123874A956"
]

theorem length02 : encoded02.length = 32 := by rfl

def bases02 : List (List Nat) := encoded02.map (fun x => x.toList.map decodeLetter)

theorem checked02 : bases02.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded03 : List String := [
  "0123879456A",
  "012387945A6",
  "01238794A56",
  "012387A4956",
  "0123897456A",
  "012389745A6",
  "01238974A56",
  "01238A45769",
  "01238A49576",
  "01238A74956",
  "0123947568A",
  "012394756A8",
  "01239475A68",
  "01239478A56",
  "0123947A568",
  "0123948567A",
  "012394856A7",
  "01239485A67",
  "0123948756A",
  "012394875A6",
  "01239487A56",
  "0123948A567",
  "0123948A756",
  "012394A5768",
  "012394A7568",
  "012394A8567",
  "012394A8756",
  "01239748A56",
  "0123987456A",
  "012398745A6",
  "01239874A56",
  "01239A45768"
]

theorem length03 : encoded03.length = 32 := by rfl

def bases03 : List (List Nat) := encoded03.map (fun x => x.toList.map decodeLetter)

theorem checked03 : bases03.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded04 : List String := [
  "01239A47568",
  "01239A48567",
  "01239A48756",
  "0123A456879",
  "0123A456897",
  "0123A456987",
  "0123A458769",
  "0123A458796",
  "0123A458976",
  "0123A459687",
  "0123A459876",
  "0123A485967",
  "0123A487596",
  "0123A487956",
  "0123A489756",
  "0123A495876",
  "0123A498756",
  "0123A745869",
  "0123A748956",
  "0123A749856",
  "0123A784956",
  "0123A845769",
  "0123A849576",
  "0123A874956",
  "0123A945768",
  "0123A947568",
  "0123A948567",
  "0123A948756",
  "0127348569A",
  "012734856A9",
  "0127348596A",
  "012734859A6"
]

theorem length04 : encoded04.length = 32 := by rfl

def bases04 : List (List Nat) := encoded04.map (fun x => x.toList.map decodeLetter)

theorem checked04 : bases04.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded05 : List String := [
  "01273485A69",
  "01273485A96",
  "0127348A596",
  "012734A8596",
  "0127384596A",
  "012738459A6",
  "01273845A96",
  "0127384A596",
  "01273A48596",
  "01273A98456",
  "0127938A456",
  "012793A8456",
  "01279A38456",
  "0127A348596",
  "0127A398456",
  "0128347569A",
  "012834756A9",
  "0128347596A",
  "012834759A6",
  "01283475A69",
  "01283475A96",
  "0128347A596",
  "012834A7596",
  "0128374569A",
  "012837456A9",
  "01283745A69",
  "0128394756A",
  "012839475A6",
  "01283947A56",
  "0128394A756",
  "012839A4756",
  "01283A47596"
]

theorem length05 : encoded05.length = 32 := by rfl

def bases05 : List (List Nat) := encoded05.map (fun x => x.toList.map decodeLetter)

theorem checked05 : bases05.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded06 : List String := [
  "01283A94756",
  "0128739456A",
  "012873945A6",
  "01287394A56",
  "0128739A456",
  "012873A9456",
  "0128793456A",
  "012879345A6",
  "01287934A56",
  "0128793A456",
  "01287A39456",
  "0128973456A",
  "012897345A6",
  "01289734A56",
  "0128973A456",
  "0128A347596",
  "0128A394756",
  "0128A739456",
  "0129348567A",
  "012934856A7",
  "01293485A67",
  "0129348A567",
  "012934A5867",
  "012934A8567",
  "0129374586A",
  "012937458A6",
  "01293745A86",
  "0129374A586",
  "0129378A456",
  "012937A4586",
  "0129384576A",
  "012938457A6"
]

theorem length06 : encoded06.length = 32 := by rfl

def bases06 : List (List Nat) := encoded06.map (fun x => x.toList.map decodeLetter)

theorem checked06 : bases06.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded07 : List String := [
  "01293845A76",
  "0129384A576",
  "0129387456A",
  "012938745A6",
  "01293874A56",
  "0129387A456",
  "012938A4576",
  "012938A7456",
  "01293A45867",
  "01293A47568",
  "01293A47586",
  "01293A48567",
  "01293A74586",
  "01293A84576",
  "01293A87456",
  "0129738A456",
  "0129873456A",
  "012987345A6",
  "01298734A56",
  "0129873A456",
  "0129A345867",
  "0129A347568",
  "0129A347586",
  "0129A348567",
  "0129A374586",
  "0129A384576",
  "0129A387456",
  "012A3456879",
  "012A3456897",
  "012A3456987",
  "012A3458769",
  "012A3458796"
]

theorem length07 : encoded07.length = 32 := by rfl

def bases07 : List (List Nat) := encoded07.map (fun x => x.toList.map decodeLetter)

theorem checked07 : bases07.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded08 : List String := [
  "012A3458976",
  "012A3459687",
  "012A3459876",
  "012A3485967",
  "012A3487596",
  "012A3487956",
  "012A3489756",
  "012A3495876",
  "012A3498756",
  "012A3745869",
  "012A3845769",
  "012A3849576",
  "012A3874956",
  "012A3879456",
  "012A3897456",
  "012A3945768",
  "012A3947568",
  "012A3948567",
  "012A3948756",
  "012A3987456",
  "012A7348596",
  "012A7389456",
  "012A7398456",
  "012A7839456",
  "012A8347596",
  "012A8394756",
  "012A8739456",
  "012A9345867",
  "012A9347568",
  "012A9347586",
  "012A9348567",
  "012A9374586"
]

theorem length08 : encoded08.length = 32 := by rfl

def bases08 : List (List Nat) := encoded08.map (fun x => x.toList.map decodeLetter)

theorem checked08 : bases08.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded09 : List String := [
  "012A9384576",
  "012A9387456",
  "0172345968A",
  "017234596A8",
  "01723459A68",
  "0172345A968",
  "0172349568A",
  "017234956A8",
  "01723495A68",
  "0172349A568",
  "017234A5968",
  "017234A9568",
  "0172384569A",
  "017238456A9",
  "0172384596A",
  "017238459A6",
  "01723845A69",
  "01723845A96",
  "0172384956A",
  "017238495A6",
  "01723849A56",
  "0172384A569",
  "0172384A596",
  "0172384A956",
  "017238A4956",
  "01723945A68",
  "0172394A568",
  "017239A4568",
  "01723A45968",
  "01723A49568",
  "01723A84956",
  "01723A94568"
]

theorem length09 : encoded09.length = 32 := by rfl

def bases09 : List (List Nat) := encoded09.map (fun x => x.toList.map decodeLetter)

theorem checked09 : bases09.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded10 : List String := [
  "0172834569A",
  "017283456A9",
  "01728345A69",
  "0172834956A",
  "017283495A6",
  "01728349A56",
  "0172834A569",
  "0172834A956",
  "017283A4956",
  "0172934568A",
  "017293456A8",
  "01729345A68",
  "0172934A568",
  "017293A4568",
  "01729A34568",
  "0172A345968",
  "0172A349568",
  "0172A384956",
  "0172A394568",
  "0172A934568",
  "0172A983456",
  "017928A3456",
  "01792A83456",
  "0179A283456",
  "017A2345968",
  "017A2349568",
  "017A2384956",
  "017A2934568",
  "017A2983456",
  "0182345967A",
  "018234596A7",
  "01823459A67"
]

theorem length10 : encoded10.length = 32 := by rfl

def bases10 : List (List Nat) := encoded10.map (fun x => x.toList.map decodeLetter)

theorem checked10 : bases10.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded11 : List String := [
  "0182345A967",
  "01823495A67",
  "0182349A567",
  "018234A5967",
  "018234A9567",
  "0182374569A",
  "018237456A9",
  "0182374596A",
  "018237459A6",
  "01823745A69",
  "01823745A96",
  "0182374956A",
  "018237495A6",
  "01823749A56",
  "0182374A569",
  "0182374A596",
  "0182374A956",
  "018237A4569",
  "018237A4956",
  "01823945A67",
  "0182394A567",
  "018239A4567",
  "01823A45967",
  "01823A49567",
  "01823A74569",
  "01823A74956",
  "01823A94567",
  "0182734596A",
  "018273459A6",
  "01827345A96",
  "0182734A596",
  "0182934567A"
]

theorem length11 : encoded11.length = 32 := by rfl

def bases11 : List (List Nat) := encoded11.map (fun x => x.toList.map decodeLetter)

theorem checked11 : bases11.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded12 : List String := [
  "018293456A7",
  "01829345A67",
  "0182934A567",
  "0182937456A",
  "018293745A6",
  "01829374A56",
  "0182937A456",
  "018293A4567",
  "018293A7456",
  "01829A34567",
  "01829A37456",
  "0182A345967",
  "0182A349567",
  "0182A374569",
  "0182A374956",
  "0182A394567",
  "0182A934567",
  "0182A937456",
  "0187293456A",
  "018729345A6",
  "01872934A56",
  "0187293A456",
  "018729A3456",
  "01872A93456",
  "0187923456A",
  "018792345A6",
  "01879234A56",
  "0187923A456",
  "018792A3456",
  "0187A293456",
  "0189723456A",
  "018972345A6"
]

theorem length12 : encoded12.length = 32 := by rfl

def bases12 : List (List Nat) := encoded12.map (fun x => x.toList.map decodeLetter)

theorem checked12 : bases12.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded13 : List String := [
  "01897234A56",
  "0189723A456",
  "018972A3456",
  "018A2345967",
  "018A2374569",
  "018A2374956",
  "018A2934567",
  "018A2937456",
  "018A7293456",
  "0192374586A",
  "0192374856A",
  "0192384576A",
  "019238457A6",
  "01923845A76",
  "0192384A576",
  "019238A4576",
  "01923A45768",
  "01923A47568",
  "01923A48567",
  "01923A48576",
  "01923A84576",
  "0192734856A",
  "019273485A6",
  "01927348A56",
  "0192734A856",
  "019273A4856",
  "019278A3456",
  "01927A34856",
  "0192834756A",
  "019283475A6",
  "01928347A56",
  "0192834A756"
]

theorem length13 : encoded13.length = 32 := by rfl

def bases13 : List (List Nat) := encoded13.map (fun x => x.toList.map decodeLetter)

theorem checked13 : bases13.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded14 : List String := [
  "019283A4756",
  "0192873456A",
  "019287345A6",
  "01928734A56",
  "0192873A456",
  "019287A3456",
  "01928A34756",
  "01928A73456",
  "0192A345768",
  "0192A347568",
  "0192A348567",
  "0192A348576",
  "0192A374586",
  "0192A374856",
  "0192A384576",
  "0192A734856",
  "0192A834756",
  "0192A873456",
  "019728A3456",
  "0198723456A",
  "019872345A6",
  "01987234A56",
  "0198723A456",
  "019872A3456",
  "019A2345768",
  "019A2347568",
  "019A2348567",
  "019A2348576",
  "019A2374586",
  "019A2374856",
  "019A2384576",
  "019A2734856"
]

theorem length14 : encoded14.length = 32 := by rfl

def bases14 : List (List Nat) := encoded14.map (fun x => x.toList.map decodeLetter)

theorem checked14 : bases14.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

def encoded15 : List String := [
  "019A2834756",
  "019A2873456",
  "01A23456879",
  "01A23456897",
  "01A23456987",
  "01A23458769",
  "01A23458796",
  "01A23458976",
  "01A23459687",
  "01A23459876",
  "01A23485967",
  "01A23487596",
  "01A23487956",
  "01A23489756",
  "01A23495876",
  "01A23498756",
  "01A23745869",
  "01A23748569",
  "01A23845769",
  "01A23849576",
  "01A23874956",
  "01A23879456",
  "01A23897456",
  "01A23945768",
  "01A23947568",
  "01A23948567",
  "01A23948756",
  "01A23987456",
  "01A27348569",
  "01A27348596",
  "01A28347569",
  "01A28347596"
]

theorem length15 : encoded15.length = 32 := by rfl

def bases15 : List (List Nat) := encoded15.map (fun x => x.toList.map decodeLetter)

theorem checked15 : bases15.all (fun x => decide (x.Perm (List.range 11))) = true := by rfl

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
  encoded14 ++
  encoded15

theorem encoded_length : encoded.length = 512 := by
  simp only [encoded, List.length_append, length00, length01, length02, length03, length04, length05, length06, length07, length08, length09, length10, length11, length12, length13, length14, length15, Nat.reduceAdd]

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
  bases14 ++
  bases15 := by
  simp only [bases, encoded, List.map_append, bases00, bases01, bases02, bases03, bases04, bases05, bases06, bases07, bases08, bases09, bases10, bases11, bases12, bases13, bases14, bases15]

theorem bases_length : bases.length = 512 := by
  rw [bases, List.length_map]
  exact encoded_length

theorem checked : bases.all (fun x => decide (x.Perm (List.range 11))) = true := by
  simp only [bases_blocks, List.all_append, checked00, checked01, checked02, checked03, checked04, checked05, checked06, checked07, checked08, checked09, checked10, checked11, checked12, checked13, checked14, checked15, Bool.and_self]

end SuperpermutationUpperBound.Native14.Certificate.EmptyLoopParts.BlockF00
