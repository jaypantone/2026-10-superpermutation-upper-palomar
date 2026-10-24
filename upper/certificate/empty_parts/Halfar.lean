module

public import upper.certificate.Checks

@[expose] public section

/-! Preserved omitted-loop strings. Every permutation check decodes at most32 strings. -/
namespace SuperpermutationUpperBound.Native14.Certificate.EmptyLoopParts.Halfar
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List String := [
  "01324567",
  "01324576",
  "01324756",
  "01327456",
  "01365247",
  "01365274",
  "01365724",
  "01367524",
  "01372456",
  "01376524",
  "01423657",
  "01423675",
  "01423765",
  "01427365",
  "01456237",
  "01456273",
  "01456723",
  "01457623",
  "01472365",
  "01475623",
  "01526347",
  "01526374",
  "01526734",
  "01527634",
  "01543267",
  "01543276",
  "01543726",
  "01547326",
  "01572634",
  "01574326",
  "01625437",
  "01625473"
]

theorem length00 : encoded00.length = 32 := by rfl

def bases00 : List (List Nat) := encoded00.map (fun x => x.toList.map decodeLetter)

theorem checked00 : bases00.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded01 : List String := [
  "01625743",
  "01627543",
  "01634257",
  "01634275",
  "01634725",
  "01637425",
  "01672543",
  "01673425",
  "01732456",
  "01736524",
  "01742365",
  "01745623",
  "01752634",
  "01754326",
  "01762543",
  "01763425",
  "02315467",
  "02315476",
  "02315746",
  "02317546",
  "02364157",
  "02364175",
  "02364715",
  "02367415",
  "02371546",
  "02376415",
  "02416357",
  "02416375",
  "02416735",
  "02417635",
  "02453167",
  "02453176"
]

theorem length01 : encoded01.length = 32 := by rfl

def bases01 : List (List Nat) := encoded01.map (fun x => x.toList.map decodeLetter)

theorem checked01 : bases01.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded02 : List String := [
  "02453716",
  "02457316",
  "02471635",
  "02475316",
  "02513647",
  "02513674",
  "02513764",
  "02517364",
  "02546137",
  "02546173",
  "02546713",
  "02547613",
  "02571364",
  "02574613",
  "02614537",
  "02614573",
  "02614753",
  "02617453",
  "02635147",
  "02635174",
  "02635714",
  "02637514",
  "02671453",
  "02673514",
  "02731546",
  "02736415",
  "02741635",
  "02745316",
  "02751364",
  "02754613",
  "02761453",
  "02763514"
]

theorem length02 : encoded02.length = 32 := by rfl

def bases02 : List (List Nat) := encoded02.map (fun x => x.toList.map decodeLetter)

theorem checked02 : bases02.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded03 : List String := [
  "03125647",
  "03125674",
  "03125764",
  "03127564",
  "03164527",
  "03164572",
  "03164752",
  "03167452",
  "03172564",
  "03176452",
  "03214657",
  "03214675",
  "03214765",
  "03217465",
  "03265417",
  "03265471",
  "03265741",
  "03267541",
  "03271465",
  "03276541",
  "03452617",
  "03452671",
  "03452761",
  "03457261",
  "03461257",
  "03461275",
  "03461725",
  "03467125",
  "03475261",
  "03476125",
  "03541627",
  "03541672"
]

theorem length03 : encoded03.length = 32 := by rfl

def bases03 : List (List Nat) := encoded03.map (fun x => x.toList.map decodeLetter)

theorem checked03 : bases03.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded04 : List String := [
  "03541762",
  "03547162",
  "03562147",
  "03562174",
  "03562714",
  "03567214",
  "03574162",
  "03576214",
  "03712564",
  "03716452",
  "03721465",
  "03726541",
  "03745261",
  "03746125",
  "03754162",
  "03756214",
  "04126537",
  "04126573",
  "04126753",
  "04127653",
  "04153627",
  "04153672",
  "04153762",
  "04157362",
  "04172653",
  "04175362",
  "04213567",
  "04213576",
  "04213756",
  "04217356",
  "04256317",
  "04256371"
]

theorem length04 : encoded04.length = 32 := by rfl

def bases04 : List (List Nat) := encoded04.map (fun x => x.toList.map decodeLetter)

theorem checked04 : bases04.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded05 : List String := [
  "04256731",
  "04257631",
  "04271356",
  "04275631",
  "04351267",
  "04351276",
  "04351726",
  "04357126",
  "04362517",
  "04362571",
  "04362751",
  "04367251",
  "04375126",
  "04376251",
  "04631527",
  "04631572",
  "04631752",
  "04637152",
  "04652137",
  "04652173",
  "04652713",
  "04657213",
  "04673152",
  "04675213",
  "04712653",
  "04715362",
  "04721356",
  "04725631",
  "04735126",
  "04736251",
  "04763152",
  "04765213"
]

theorem length05 : encoded05.length = 32 := by rfl

def bases05 : List (List Nat) := encoded05.map (fun x => x.toList.map decodeLetter)

theorem checked05 : bases05.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded06 : List String := [
  "05123467",
  "05123476",
  "05123746",
  "05127346",
  "05146327",
  "05146372",
  "05146732",
  "05147632",
  "05172346",
  "05174632",
  "05216437",
  "05216473",
  "05216743",
  "05217643",
  "05243617",
  "05243671",
  "05243761",
  "05247361",
  "05271643",
  "05274361",
  "05342167",
  "05342176",
  "05342716",
  "05347216",
  "05361427",
  "05361472",
  "05361742",
  "05367142",
  "05374216",
  "05376142",
  "05632417",
  "05632471"
]

theorem length06 : encoded06.length = 32 := by rfl

def bases06 : List (List Nat) := encoded06.map (fun x => x.toList.map decodeLetter)

theorem checked06 : bases06.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded07 : List String := [
  "05632741",
  "05637241",
  "05641237",
  "05641273",
  "05641723",
  "05647123",
  "05673241",
  "05674123",
  "05712346",
  "05714632",
  "05721643",
  "05724361",
  "05734216",
  "05736142",
  "05763241",
  "05764123",
  "06124357",
  "06124375",
  "06124735",
  "06127435",
  "06135427",
  "06135472",
  "06135742",
  "06137542",
  "06172435",
  "06173542",
  "06215347",
  "06215374",
  "06215734",
  "06217534",
  "06234517",
  "06234571"
]

theorem length07 : encoded07.length = 32 := by rfl

def bases07 : List (List Nat) := encoded07.map (fun x => x.toList.map decodeLetter)

theorem checked07 : bases07.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded08 : List String := [
  "06234751",
  "06237451",
  "06271534",
  "06273451",
  "06432157",
  "06432175",
  "06432715",
  "06437215",
  "06451327",
  "06451372",
  "06451732",
  "06457132",
  "06473215",
  "06475132",
  "06531247",
  "06531274",
  "06531724",
  "06537124",
  "06542317",
  "06542371",
  "06542731",
  "06547231",
  "06573124",
  "06574231",
  "06712435",
  "06713542",
  "06721534",
  "06723451",
  "06743215",
  "06745132",
  "06753124",
  "06754231"
]

theorem length08 : encoded08.length = 32 := by rfl

def bases08 : List (List Nat) := encoded08.map (fun x => x.toList.map decodeLetter)

theorem checked08 : bases08.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded09 : List String := [
  "07132456",
  "07136524",
  "07142365",
  "07145623",
  "07152634",
  "07154326",
  "07162543",
  "07163425",
  "07231546",
  "07236415",
  "07241635",
  "07245316",
  "07251364",
  "07254613",
  "07261453",
  "07263514",
  "07312564",
  "07316452",
  "07321465",
  "07326541",
  "07345261",
  "07346125",
  "07354162",
  "07356214",
  "07412653",
  "07415362",
  "07421356",
  "07425631",
  "07435126",
  "07436251",
  "07463152",
  "07465213"
]

theorem length09 : encoded09.length = 32 := by rfl

def bases09 : List (List Nat) := encoded09.map (fun x => x.toList.map decodeLetter)

theorem checked09 : bases09.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

def encoded10 : List String := [
  "07512346",
  "07514632",
  "07521643",
  "07524361",
  "07534216",
  "07536142",
  "07563241",
  "07564123",
  "07612435",
  "07613542",
  "07621534",
  "07623451",
  "07643215",
  "07645132",
  "07653124",
  "07654231"
]

theorem length10 : encoded10.length = 16 := by rfl

def bases10 : List (List Nat) := encoded10.map (fun x => x.toList.map decodeLetter)

theorem checked10 : bases10.all (fun x => decide (x.Perm (List.range 8))) = true := by rfl

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
  encoded10

theorem encoded_length : encoded.length = 336 := by
  simp only [encoded, List.length_append, length00, length01, length02, length03, length04, length05, length06, length07, length08, length09, length10, Nat.reduceAdd]

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
  bases10 := by
  simp only [bases, encoded, List.map_append, bases00, bases01, bases02, bases03, bases04, bases05, bases06, bases07, bases08, bases09, bases10]

theorem bases_length : bases.length = 336 := by
  rw [bases, List.length_map]
  exact encoded_length

theorem checked : bases.all (fun x => decide (x.Perm (List.range 8))) = true := by
  simp only [bases_blocks, List.all_append, checked00, checked01, checked02, checked03, checked04, checked05, checked06, checked07, checked08, checked09, checked10, Bool.and_self]

end SuperpermutationUpperBound.Native14.Certificate.EmptyLoopParts.Halfar
