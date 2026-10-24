module

public import upper.pointers.Checker
public import upper.pointers.FastCircles

@[expose] public section

/-! Connector incidences 122368 through 122495.
Each kernel reduction checks at most 32 witnesses. Concatenation is structural.
The witness integers remain untrusted inputs to the proved checker. -/
namespace SuperpermutationUpperBound.Native14.Pointers.Chunks.C239
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable def entries00 : List Nat := [42056811236, 76416549908, 31234462660, 46610776669, 37835767949, 26552566471, 20836779179, 12246843551, 3656908959, 89570411519, 79158051183, 74313106641, 45364548899, 52316078875, 67845488887, 38020842373, 29245833651, 17962632173, 29133112120, 20839923956, 10100409848, 1510475256, 87789930110, 79116633850, 69571970064, 64559776330, 33485751018, 59255554345, 36191077920, 27601142874, 20543177072, 12249990938]
theorem length00 : entries00.length = 32 := by rfl
theorem checked00 : rangeCheck (checkEntry FastCircles.circleAt)
    122368 entries00 = true := by decide +kernel
noncomputable def entries01 : List Nat := [3660056346, 87409820730, 79199995062, 70526698802, 60982035018, 45013275499, 46606059040, 35252077822, 19011208282, 11953242480, 3363307888, 89559402266, 78819886138, 70610060470, 61936764210, 52392100426, 53603210092, 38016124448, 26662143230, 18072208184, 10421273234, 1831338642, 89262655392, 80969467228, 70229951090, 62020125422, 53346829164, 62193144685, 57228661167, 29426189402, 20836254354, 9482273136]
theorem length01 : entries01.length = 32 := by rfl
theorem checked01 : rangeCheck (checkEntry FastCircles.circleAt)
    122400 entries01 = true := by decide +kernel
noncomputable def entries02 : List Nat := [892338544, 87730684116, 80672720344, 72379532180, 61640016042, 53430190376, 70783079278, 65818595760, 30200038654, 21610103608, 12246319316, 3656384724, 86791686048, 79140751098, 72082785296, 63789597132, 53050083026, 79373013871, 74408530353, 26622297342, 18032362296, 13020168560, 4430233968, 89555732218, 78201751000, 70550816050, 63492850250, 55199662086, 87962948464, 82998464946, 27577026080, 18987091034]
theorem length02 : entries02.length = 32 := by rfl
theorem checked02 : rangeCheck (checkEntry FastCircles.circleAt)
    122432 entries02 = true := by decide +kernel
noncomputable def entries03 : List Nat := [9442427248, 852492656, 90329581472, 80965797170, 69611815952, 61960881004, 10653537137, 2063602545, 91588399539, 27660387292, 19070452246, 10397155986, 1807221394, 86751840160, 81739646424, 72375862124, 61021880906, 19243471730, 14278988212, 5689053620, 27280277912, 18690344896, 10480517198, 1890582606, 87706566868, 78161905112, 73149711376, 85006483536, 42075685610, 22868922805, 37723047166, 29429859002]
theorem length03 : entries03.length = 32 := by rfl
theorem checked03 : rangeCheck (checkEntry FastCircles.circleAt)
    122464 entries03 = true := by decide +kernel

noncomputable def entries : List Nat :=
  entries00 ++
  entries01 ++
  entries02 ++
  entries03
theorem entries_length : entries.length = 128 := by
  simp only [entries, List.length_append, length00, length01, length02, length03, Nat.reduceAdd]
theorem checked : rangeCheck (checkEntry FastCircles.circleAt)
    122368 entries = true := by
  simp only [entries, rangeCheck_append, List.length_append,
    length00, length01, length02, length03, Nat.reduceAdd, checked00, checked01, checked02, checked03, Bool.and_self]
end SuperpermutationUpperBound.Native14.Pointers.Chunks.C239
