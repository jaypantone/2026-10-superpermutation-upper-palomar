module

public import upper.pointers.PointTree
public import upper.certificate.BlockF0Prefixes

@[expose] public section

/-! Balanced source-point data. Both projections are kernel checked once;
lookup soundness then follows from literal membership in this tree. -/
namespace SuperpermutationUpperBound.Native14.Pointers.FastBlockF0
open Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

noncomputable def tree : PointTree :=
  .branch 357
  (.branch 178
    (.branch 89
      (.branch 44
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("0123456789A", 9), 0⟩, ⟨decodeRow 12 ("A0123456798", 9), -1⟩, ⟨decodeRow 12 ("8A012345697", 11), -2⟩, ⟨decodeRow 12 ("A0123456987", 9), -1⟩, ⟨decodeRow 12 ("7A012345689", 11), -2⟩])
              (.leaf [⟨decodeRow 12 ("A0123456879", 11), -1⟩, ⟨decodeRow 12 ("012345687A9", 9), 0⟩, ⟨decodeRow 12 ("901234568A7", 11), -1⟩, ⟨decodeRow 12 ("01234568A97", 9), 0⟩, ⟨decodeRow 12 ("7012345689A", 9), -1⟩, ⟨decodeRow 12 ("A7012345698", 11), -2⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("701234569A8", 9), -1⟩, ⟨decodeRow 12 ("870123456A9", 11), -2⟩, ⟨decodeRow 12 ("70123456A89", 11), -1⟩, ⟨decodeRow 12 ("0123456A879", 9), 0⟩, ⟨decodeRow 12 ("90123456A78", 11), -1⟩])
              (.leaf [⟨decodeRow 12 ("0123456A798", 9), 0⟩, ⟨decodeRow 12 ("80123456A97", 9), -1⟩, ⟨decodeRow 12 ("7801234569A", 9), -2⟩, ⟨decodeRow 12 ("A7801234596", 11), -3⟩, ⟨decodeRow 12 ("780123459A6", 9), -2⟩, ⟨decodeRow 12 ("678012345A9", 11), -3⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("78012345A69", 11), -2⟩, ⟨decodeRow 12 ("8012345A679", 11), -1⟩, ⟨decodeRow 12 ("012345A6789", 11), 0⟩, ⟨decodeRow 12 ("12345A67809", 9), 1⟩, ⟨decodeRow 12 ("912345A6708", 11), 0⟩])
              (.leaf [⟨decodeRow 12 ("12345A67098", 9), 1⟩, ⟨decodeRow 12 ("812345A6790", 9), 0⟩, ⟨decodeRow 12 ("0812345A697", 11), -1⟩, ⟨decodeRow 12 ("812345A6907", 9), 0⟩, ⟨decodeRow 12 ("7812345A609", 11), -1⟩, ⟨decodeRow 12 ("812345A6079", 11), 0⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("12345A60789", 11), 1⟩, ⟨decodeRow 12 ("2345A607819", 9), 2⟩, ⟨decodeRow 12 ("92345A60718", 11), 1⟩, ⟨decodeRow 12 ("2345A607198", 9), 2⟩, ⟨decodeRow 12 ("82345A60791", 9), 1⟩])
              (.leaf [⟨decodeRow 12 ("182345A6097", 11), 0⟩, ⟨decodeRow 12 ("82345A60917", 9), 1⟩, ⟨decodeRow 12 ("782345A6019", 11), 0⟩, ⟨decodeRow 12 ("82345A60179", 11), 1⟩, ⟨decodeRow 12 ("2345A601789", 11), 2⟩, ⟨decodeRow 12 ("345A6017829", 9), 3⟩]))))
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("9345A601728", 11), 2⟩, ⟨decodeRow 12 ("345A6017298", 9), 3⟩, ⟨decodeRow 12 ("8345A601792", 9), 2⟩, ⟨decodeRow 12 ("28345A60197", 11), 1⟩, ⟨decodeRow 12 ("8345A601927", 9), 2⟩])
              (.leaf [⟨decodeRow 12 ("78345A60129", 11), 1⟩, ⟨decodeRow 12 ("8345A601279", 11), 2⟩, ⟨decodeRow 12 ("345A6012789", 11), 3⟩, ⟨decodeRow 12 ("45A60127839", 9), 4⟩, ⟨decodeRow 12 ("945A6012738", 11), 3⟩, ⟨decodeRow 12 ("45A60127398", 9), 4⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("845A6012793", 9), 3⟩, ⟨decodeRow 12 ("3845A601297", 11), 2⟩, ⟨decodeRow 12 ("845A6012937", 9), 3⟩, ⟨decodeRow 12 ("7845A601239", 11), 2⟩, ⟨decodeRow 12 ("845A6012379", 11), 3⟩])
              (.leaf [⟨decodeRow 12 ("45A60123789", 11), 4⟩, ⟨decodeRow 12 ("5A601237849", 9), 5⟩, ⟨decodeRow 12 ("95A60123748", 11), 4⟩, ⟨decodeRow 12 ("5A601237498", 9), 5⟩, ⟨decodeRow 12 ("85A60123794", 9), 4⟩, ⟨decodeRow 12 ("485A6012397", 11), 3⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("85A60123947", 9), 4⟩, ⟨decodeRow 12 ("785A6012349", 11), 3⟩, ⟨decodeRow 12 ("85A60123479", 11), 4⟩, ⟨decodeRow 12 ("5A601234789", 11), 5⟩, ⟨decodeRow 12 ("A6012347859", 11), 6⟩])
              (.leaf [⟨decodeRow 12 ("601234785A9", 9), 7⟩, ⟨decodeRow 12 ("960123478A5", 11), 6⟩, ⟨decodeRow 12 ("60123478A95", 9), 7⟩, ⟨decodeRow 12 ("5601234789A", 9), 6⟩, ⟨decodeRow 12 ("A5601234798", 9), 5⟩, ⟨decodeRow 12 ("8A560123497", 11), 4⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("A5601234987", 9), 5⟩, ⟨decodeRow 12 ("7A560123489", 11), 4⟩, ⟨decodeRow 12 ("A5601234879", 11), 5⟩, ⟨decodeRow 12 ("560123487A9", 9), 6⟩, ⟨decodeRow 12 ("956012348A7", 11), 5⟩, ⟨decodeRow 12 ("56012348A97", 9), 6⟩])
              (.leaf [⟨decodeRow 12 ("7560123489A", 9), 5⟩, ⟨decodeRow 12 ("A7560123498", 11), 4⟩, ⟨decodeRow 12 ("756012349A8", 9), 5⟩, ⟨decodeRow 12 ("875601234A9", 11), 4⟩, ⟨decodeRow 12 ("75601234A89", 11), 5⟩, ⟨decodeRow 12 ("5601234A879", 9), 6⟩])))))
      (.branch 44
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("95601234A78", 11), 5⟩, ⟨decodeRow 12 ("5601234A798", 9), 6⟩, ⟨decodeRow 12 ("85601234A97", 9), 5⟩, ⟨decodeRow 12 ("7856012349A", 9), 4⟩, ⟨decodeRow 12 ("A7856012394", 11), 3⟩])
              (.leaf [⟨decodeRow 12 ("785601239A4", 9), 4⟩, ⟨decodeRow 12 ("478560123A9", 11), 3⟩, ⟨decodeRow 12 ("78560123A49", 11), 4⟩, ⟨decodeRow 12 ("8560123A479", 11), 5⟩, ⟨decodeRow 12 ("560123A4789", 11), 6⟩, ⟨decodeRow 12 ("60123A47859", 9), 7⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("960123A4758", 11), 6⟩, ⟨decodeRow 12 ("60123A47598", 9), 7⟩, ⟨decodeRow 12 ("860123A4795", 9), 6⟩, ⟨decodeRow 12 ("5860123A497", 11), 5⟩, ⟨decodeRow 12 ("860123A4957", 9), 6⟩])
              (.leaf [⟨decodeRow 12 ("7860123A459", 11), 5⟩, ⟨decodeRow 12 ("860123A4579", 11), 6⟩, ⟨decodeRow 12 ("60123A45789", 11), 7⟩, ⟨decodeRow 12 ("0123A457869", 9), 8⟩, ⟨decodeRow 12 ("90123A45768", 11), 7⟩, ⟨decodeRow 12 ("0123A457698", 9), 8⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("80123A45796", 9), 7⟩, ⟨decodeRow 12 ("680123A4597", 11), 6⟩, ⟨decodeRow 12 ("80123A45967", 9), 7⟩, ⟨decodeRow 12 ("780123A4569", 11), 6⟩, ⟨decodeRow 12 ("80123A45679", 11), 7⟩])
              (.leaf [⟨decodeRow 12 ("0123A456789", 11), 8⟩, ⟨decodeRow 12 ("123A4567809", 9), 9⟩, ⟨decodeRow 12 ("9123A456708", 11), 8⟩, ⟨decodeRow 12 ("123A4567098", 9), 9⟩, ⟨decodeRow 12 ("8123A456790", 9), 8⟩, ⟨decodeRow 12 ("08123A45697", 11), 7⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("8123A456907", 9), 8⟩, ⟨decodeRow 12 ("78123A45609", 11), 7⟩, ⟨decodeRow 12 ("8123A456079", 11), 8⟩, ⟨decodeRow 12 ("123A4560789", 11), 9⟩, ⟨decodeRow 12 ("23A45607819", 9), 10⟩])
              (.leaf [⟨decodeRow 12 ("923A4560718", 11), 9⟩, ⟨decodeRow 12 ("23A45607198", 9), 10⟩, ⟨decodeRow 12 ("823A4560791", 9), 9⟩, ⟨decodeRow 12 ("1823A456097", 11), 8⟩, ⟨decodeRow 12 ("823A4560917", 9), 9⟩, ⟨decodeRow 12 ("7823A456019", 11), 8⟩]))))
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("823A4560179", 11), 9⟩, ⟨decodeRow 12 ("23A45601789", 11), 10⟩, ⟨decodeRow 12 ("3A456017829", 9), 11⟩, ⟨decodeRow 12 ("93A45601728", 11), 10⟩, ⟨decodeRow 12 ("3A456017298", 9), 11⟩])
              (.leaf [⟨decodeRow 12 ("83A45601792", 9), 10⟩, ⟨decodeRow 12 ("283A4560197", 11), 9⟩, ⟨decodeRow 12 ("83A45601927", 9), 10⟩, ⟨decodeRow 12 ("783A4560129", 11), 9⟩, ⟨decodeRow 12 ("83A45601279", 11), 10⟩, ⟨decodeRow 12 ("3A456012789", 11), 11⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("A4560127839", 11), 12⟩, ⟨decodeRow 12 ("456012783A9", 9), 13⟩, ⟨decodeRow 12 ("945601278A3", 11), 12⟩, ⟨decodeRow 12 ("45601278A93", 9), 13⟩, ⟨decodeRow 12 ("3456012789A", 9), 12⟩])
              (.leaf [⟨decodeRow 12 ("A3456012798", 9), 11⟩, ⟨decodeRow 12 ("8A345601297", 11), 10⟩, ⟨decodeRow 12 ("A3456012987", 9), 11⟩, ⟨decodeRow 12 ("7A345601289", 11), 10⟩, ⟨decodeRow 12 ("A3456012879", 11), 11⟩, ⟨decodeRow 12 ("345601287A9", 9), 12⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("934560128A7", 11), 11⟩, ⟨decodeRow 12 ("34560128A97", 9), 12⟩, ⟨decodeRow 12 ("7345601289A", 9), 11⟩, ⟨decodeRow 12 ("A7345601298", 11), 10⟩, ⟨decodeRow 12 ("734560129A8", 9), 11⟩])
              (.leaf [⟨decodeRow 12 ("873456012A9", 11), 10⟩, ⟨decodeRow 12 ("73456012A89", 11), 11⟩, ⟨decodeRow 12 ("3456012A879", 9), 12⟩, ⟨decodeRow 12 ("93456012A78", 11), 11⟩, ⟨decodeRow 12 ("3456012A798", 9), 12⟩, ⟨decodeRow 12 ("83456012A97", 9), 11⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("7834560129A", 9), 10⟩, ⟨decodeRow 12 ("A7834560192", 11), 9⟩, ⟨decodeRow 12 ("783456019A2", 9), 10⟩, ⟨decodeRow 12 ("278345601A9", 11), 9⟩, ⟨decodeRow 12 ("78345601A29", 11), 10⟩, ⟨decodeRow 12 ("8345601A279", 11), 11⟩])
              (.leaf [⟨decodeRow 12 ("345601A2789", 11), 12⟩, ⟨decodeRow 12 ("45601A27839", 9), 13⟩, ⟨decodeRow 12 ("945601A2738", 11), 12⟩, ⟨decodeRow 12 ("45601A27398", 9), 13⟩, ⟨decodeRow 12 ("845601A2793", 9), 12⟩, ⟨decodeRow 12 ("3845601A297", 11), 11⟩]))))))
    (.branch 89
      (.branch 44
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("845601A2937", 9), 12⟩, ⟨decodeRow 12 ("7845601A239", 11), 11⟩, ⟨decodeRow 12 ("845601A2379", 11), 12⟩, ⟨decodeRow 12 ("45601A23789", 11), 13⟩, ⟨decodeRow 12 ("5601A237849", 9), 14⟩])
              (.leaf [⟨decodeRow 12 ("95601A23748", 11), 13⟩, ⟨decodeRow 12 ("5601A237498", 9), 14⟩, ⟨decodeRow 12 ("85601A23794", 9), 13⟩, ⟨decodeRow 12 ("485601A2397", 11), 12⟩, ⟨decodeRow 12 ("85601A23947", 9), 13⟩, ⟨decodeRow 12 ("785601A2349", 11), 12⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("85601A23479", 11), 13⟩, ⟨decodeRow 12 ("5601A234789", 11), 14⟩, ⟨decodeRow 12 ("601A2347859", 9), 15⟩, ⟨decodeRow 12 ("9601A234758", 11), 14⟩, ⟨decodeRow 12 ("601A2347598", 9), 15⟩])
              (.leaf [⟨decodeRow 12 ("8601A234795", 9), 14⟩, ⟨decodeRow 12 ("58601A23497", 11), 13⟩, ⟨decodeRow 12 ("8601A234957", 9), 14⟩, ⟨decodeRow 12 ("78601A23459", 11), 13⟩, ⟨decodeRow 12 ("8601A234579", 11), 14⟩, ⟨decodeRow 12 ("601A2345789", 11), 15⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("01A23457869", 9), 16⟩, ⟨decodeRow 12 ("901A2345768", 11), 15⟩, ⟨decodeRow 12 ("01A23457698", 9), 16⟩, ⟨decodeRow 12 ("801A2345796", 9), 15⟩, ⟨decodeRow 12 ("6801A234597", 11), 14⟩])
              (.leaf [⟨decodeRow 12 ("801A2345967", 9), 15⟩, ⟨decodeRow 12 ("7801A234569", 11), 14⟩, ⟨decodeRow 12 ("801A2345679", 11), 15⟩, ⟨decodeRow 12 ("01A23456789", 11), 16⟩, ⟨decodeRow 12 ("1A234567809", 9), 17⟩, ⟨decodeRow 12 ("91A23456708", 11), 16⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("1A234567098", 9), 17⟩, ⟨decodeRow 12 ("81A23456790", 9), 16⟩, ⟨decodeRow 12 ("081A2345697", 11), 15⟩, ⟨decodeRow 12 ("81A23456907", 9), 16⟩, ⟨decodeRow 12 ("781A2345609", 11), 15⟩])
              (.leaf [⟨decodeRow 12 ("81A23456079", 11), 16⟩, ⟨decodeRow 12 ("1A234560789", 11), 17⟩, ⟨decodeRow 12 ("A2345607819", 11), 18⟩, ⟨decodeRow 12 ("234560781A9", 9), 19⟩, ⟨decodeRow 12 ("923456078A1", 11), 18⟩, ⟨decodeRow 12 ("23456078A91", 9), 19⟩]))))
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("1234560789A", 9), 18⟩, ⟨decodeRow 12 ("A1234560798", 9), 17⟩, ⟨decodeRow 12 ("8A123456097", 11), 16⟩, ⟨decodeRow 12 ("A1234560987", 9), 17⟩, ⟨decodeRow 12 ("7A123456089", 11), 16⟩])
              (.leaf [⟨decodeRow 12 ("A1234560879", 11), 17⟩, ⟨decodeRow 12 ("123456087A9", 9), 18⟩, ⟨decodeRow 12 ("912345608A7", 11), 17⟩, ⟨decodeRow 12 ("12345608A97", 9), 18⟩, ⟨decodeRow 12 ("7123456089A", 9), 17⟩, ⟨decodeRow 12 ("A7123456098", 11), 16⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("712345609A8", 9), 17⟩, ⟨decodeRow 12 ("871234560A9", 11), 16⟩, ⟨decodeRow 12 ("71234560A89", 11), 17⟩, ⟨decodeRow 12 ("1234560A879", 9), 18⟩, ⟨decodeRow 12 ("91234560A78", 11), 17⟩])
              (.leaf [⟨decodeRow 12 ("1234560A798", 9), 18⟩, ⟨decodeRow 12 ("81234560A97", 9), 17⟩, ⟨decodeRow 12 ("7812345609A", 9), 16⟩, ⟨decodeRow 12 ("A7812345690", 11), 15⟩, ⟨decodeRow 12 ("781234569A0", 9), 16⟩, ⟨decodeRow 12 ("078123456A9", 11), 15⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("78123456A09", 11), 16⟩, ⟨decodeRow 12 ("8123456A079", 11), 17⟩, ⟨decodeRow 12 ("123456A0789", 11), 18⟩, ⟨decodeRow 12 ("23456A07819", 9), 19⟩, ⟨decodeRow 12 ("923456A0718", 11), 18⟩])
              (.leaf [⟨decodeRow 12 ("23456A07198", 9), 19⟩, ⟨decodeRow 12 ("823456A0791", 9), 18⟩, ⟨decodeRow 12 ("1823456A097", 11), 17⟩, ⟨decodeRow 12 ("823456A0917", 9), 18⟩, ⟨decodeRow 12 ("7823456A019", 11), 17⟩, ⟨decodeRow 12 ("823456A0179", 11), 18⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("23456A01789", 11), 19⟩, ⟨decodeRow 12 ("3456A017829", 9), 20⟩, ⟨decodeRow 12 ("93456A01728", 11), 19⟩, ⟨decodeRow 12 ("3456A017298", 9), 20⟩, ⟨decodeRow 12 ("83456A01792", 9), 19⟩, ⟨decodeRow 12 ("283456A0197", 11), 18⟩])
              (.leaf [⟨decodeRow 12 ("83456A01927", 9), 19⟩, ⟨decodeRow 12 ("783456A0129", 11), 18⟩, ⟨decodeRow 12 ("83456A01279", 11), 19⟩, ⟨decodeRow 12 ("3456A012789", 11), 20⟩, ⟨decodeRow 12 ("456A0127839", 9), 21⟩, ⟨decodeRow 12 ("9456A012738", 11), 20⟩])))))
      (.branch 45
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("456A0127398", 9), 21⟩, ⟨decodeRow 12 ("8456A012793", 9), 20⟩, ⟨decodeRow 12 ("38456A01297", 11), 19⟩, ⟨decodeRow 12 ("8456A012937", 9), 20⟩, ⟨decodeRow 12 ("78456A01239", 11), 19⟩])
              (.leaf [⟨decodeRow 12 ("8456A012379", 11), 20⟩, ⟨decodeRow 12 ("456A0123789", 11), 21⟩, ⟨decodeRow 12 ("56A01237849", 9), 22⟩, ⟨decodeRow 12 ("956A0123748", 11), 21⟩, ⟨decodeRow 12 ("56A01237498", 9), 22⟩, ⟨decodeRow 12 ("856A0123794", 9), 21⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("4856A012397", 11), 20⟩, ⟨decodeRow 12 ("856A0123947", 9), 21⟩, ⟨decodeRow 12 ("7856A012349", 11), 20⟩, ⟨decodeRow 12 ("856A0123479", 11), 21⟩, ⟨decodeRow 12 ("56A01234789", 11), 22⟩])
              (.leaf [⟨decodeRow 12 ("6A012347859", 9), 23⟩, ⟨decodeRow 12 ("96A01234758", 11), 22⟩, ⟨decodeRow 12 ("6A012347598", 9), 23⟩, ⟨decodeRow 12 ("86A01234795", 9), 22⟩, ⟨decodeRow 12 ("586A0123497", 11), 21⟩, ⟨decodeRow 12 ("86A01234957", 9), 22⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("786A0123459", 11), 21⟩, ⟨decodeRow 12 ("86A01234579", 11), 22⟩, ⟨decodeRow 12 ("6A012345789", 11), 23⟩, ⟨decodeRow 12 ("A0123457869", 11), 24⟩, ⟨decodeRow 12 ("012345786A9", 9), 25⟩])
              (.leaf [⟨decodeRow 12 ("901234578A6", 11), 24⟩, ⟨decodeRow 12 ("01234578A96", 9), 25⟩, ⟨decodeRow 12 ("6012345789A", 9), 24⟩, ⟨decodeRow 12 ("A6012345798", 9), 23⟩, ⟨decodeRow 12 ("8A601234597", 11), 22⟩, ⟨decodeRow 12 ("A6012345987", 9), 23⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("7A601234589", 11), 22⟩, ⟨decodeRow 12 ("A6012345879", 11), 23⟩, ⟨decodeRow 12 ("601234587A9", 9), 24⟩, ⟨decodeRow 12 ("960123458A7", 11), 23⟩, ⟨decodeRow 12 ("60123458A97", 9), 24⟩, ⟨decodeRow 12 ("7601234589A", 9), 23⟩])
              (.leaf [⟨decodeRow 12 ("A7601234598", 11), 22⟩, ⟨decodeRow 12 ("760123459A8", 9), 23⟩, ⟨decodeRow 12 ("876012345A9", 11), 22⟩, ⟨decodeRow 12 ("76012345A89", 11), 23⟩, ⟨decodeRow 12 ("6012345A879", 9), 24⟩, ⟨decodeRow 12 ("96012345A78", 11), 23⟩]))))
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("6012345A798", 9), 24⟩, ⟨decodeRow 12 ("86012345A97", 9), 23⟩, ⟨decodeRow 12 ("7860123459A", 9), 22⟩, ⟨decodeRow 12 ("A7860123495", 11), 21⟩, ⟨decodeRow 12 ("786012349A5", 9), 22⟩])
              (.leaf [⟨decodeRow 12 ("578601234A9", 11), 21⟩, ⟨decodeRow 12 ("78601234A59", 11), 22⟩, ⟨decodeRow 12 ("8601234A579", 11), 23⟩, ⟨decodeRow 12 ("601234A5789", 11), 24⟩, ⟨decodeRow 12 ("01234A57869", 9), 25⟩, ⟨decodeRow 12 ("901234A5768", 11), 24⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("01234A57698", 9), 25⟩, ⟨decodeRow 12 ("801234A5796", 9), 24⟩, ⟨decodeRow 12 ("6801234A597", 11), 23⟩, ⟨decodeRow 12 ("801234A5967", 9), 24⟩, ⟨decodeRow 12 ("7801234A569", 11), 23⟩])
              (.leaf [⟨decodeRow 12 ("801234A5679", 11), 24⟩, ⟨decodeRow 12 ("01234A56789", 11), 25⟩, ⟨decodeRow 12 ("1234A567809", 9), 26⟩, ⟨decodeRow 12 ("91234A56708", 11), 25⟩, ⟨decodeRow 12 ("1234A567098", 9), 26⟩, ⟨decodeRow 12 ("81234A56790", 9), 25⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("081234A5697", 11), 24⟩, ⟨decodeRow 12 ("81234A56907", 9), 25⟩, ⟨decodeRow 12 ("781234A5609", 11), 24⟩, ⟨decodeRow 12 ("81234A56079", 11), 25⟩, ⟨decodeRow 12 ("1234A560789", 11), 26⟩])
              (.leaf [⟨decodeRow 12 ("234A5607819", 9), 27⟩, ⟨decodeRow 12 ("9234A560718", 11), 26⟩, ⟨decodeRow 12 ("234A5607198", 9), 27⟩, ⟨decodeRow 12 ("8234A560791", 9), 26⟩, ⟨decodeRow 12 ("18234A56097", 11), 25⟩, ⟨decodeRow 12 ("8234A560917", 9), 26⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("78234A56019", 11), 25⟩, ⟨decodeRow 12 ("8234A560179", 11), 26⟩, ⟨decodeRow 12 ("234A5601789", 11), 27⟩, ⟨decodeRow 12 ("34A56017829", 9), 28⟩, ⟨decodeRow 12 ("934A5601728", 11), 27⟩, ⟨decodeRow 12 ("34A56017298", 9), 28⟩])
              (.leaf [⟨decodeRow 12 ("834A5601792", 9), 27⟩, ⟨decodeRow 12 ("2834A560197", 11), 26⟩, ⟨decodeRow 12 ("834A5601927", 9), 27⟩, ⟨decodeRow 12 ("7834A560129", 11), 26⟩, ⟨decodeRow 12 ("834A5601279", 11), 27⟩, ⟨decodeRow 12 ("34A56012789", 11), 28⟩])))))))
  (.branch 178
    (.branch 89
      (.branch 44
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("4A560127839", 9), 29⟩, ⟨decodeRow 12 ("94A56012738", 11), 28⟩, ⟨decodeRow 12 ("4A560127398", 9), 29⟩, ⟨decodeRow 12 ("84A56012793", 9), 28⟩, ⟨decodeRow 12 ("384A5601297", 11), 27⟩])
              (.leaf [⟨decodeRow 12 ("84A56012937", 9), 28⟩, ⟨decodeRow 12 ("784A5601239", 11), 27⟩, ⟨decodeRow 12 ("84A56012379", 11), 28⟩, ⟨decodeRow 12 ("4A560123789", 11), 29⟩, ⟨decodeRow 12 ("A5601237849", 11), 30⟩, ⟨decodeRow 12 ("560123784A9", 9), 31⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("956012378A4", 11), 30⟩, ⟨decodeRow 12 ("56012378A94", 9), 31⟩, ⟨decodeRow 12 ("4560123789A", 9), 30⟩, ⟨decodeRow 12 ("A4560123798", 9), 29⟩, ⟨decodeRow 12 ("8A456012397", 11), 28⟩])
              (.leaf [⟨decodeRow 12 ("A4560123987", 9), 29⟩, ⟨decodeRow 12 ("7A456012389", 11), 28⟩, ⟨decodeRow 12 ("A4560123879", 11), 29⟩, ⟨decodeRow 12 ("456012387A9", 9), 30⟩, ⟨decodeRow 12 ("945601238A7", 11), 29⟩, ⟨decodeRow 12 ("45601238A97", 9), 30⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("7456012389A", 9), 29⟩, ⟨decodeRow 12 ("A7456012398", 11), 28⟩, ⟨decodeRow 12 ("745601239A8", 9), 29⟩, ⟨decodeRow 12 ("874560123A9", 11), 28⟩, ⟨decodeRow 12 ("74560123A89", 11), 29⟩])
              (.leaf [⟨decodeRow 12 ("4560123A879", 9), 30⟩, ⟨decodeRow 12 ("94560123A78", 11), 29⟩, ⟨decodeRow 12 ("4560123A798", 9), 30⟩, ⟨decodeRow 12 ("84560123A97", 9), 29⟩, ⟨decodeRow 12 ("7845601239A", 9), 28⟩, ⟨decodeRow 12 ("A7845601293", 11), 27⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("784560129A3", 9), 28⟩, ⟨decodeRow 12 ("378456012A9", 11), 27⟩, ⟨decodeRow 12 ("78456012A39", 11), 28⟩, ⟨decodeRow 12 ("8456012A379", 11), 29⟩, ⟨decodeRow 12 ("456012A3789", 11), 30⟩])
              (.leaf [⟨decodeRow 12 ("56012A37849", 9), 31⟩, ⟨decodeRow 12 ("956012A3748", 11), 30⟩, ⟨decodeRow 12 ("56012A37498", 9), 31⟩, ⟨decodeRow 12 ("856012A3794", 9), 30⟩, ⟨decodeRow 12 ("4856012A397", 11), 29⟩, ⟨decodeRow 12 ("856012A3947", 9), 30⟩]))))
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("7856012A349", 11), 29⟩, ⟨decodeRow 12 ("856012A3479", 11), 30⟩, ⟨decodeRow 12 ("56012A34789", 11), 31⟩, ⟨decodeRow 12 ("6012A347859", 9), 32⟩, ⟨decodeRow 12 ("96012A34758", 11), 31⟩])
              (.leaf [⟨decodeRow 12 ("6012A347598", 9), 32⟩, ⟨decodeRow 12 ("86012A34795", 9), 31⟩, ⟨decodeRow 12 ("586012A3497", 11), 30⟩, ⟨decodeRow 12 ("86012A34957", 9), 31⟩, ⟨decodeRow 12 ("786012A3459", 11), 30⟩, ⟨decodeRow 12 ("86012A34579", 11), 31⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("6012A345789", 11), 32⟩, ⟨decodeRow 12 ("012A3457869", 9), 33⟩, ⟨decodeRow 12 ("9012A345768", 11), 32⟩, ⟨decodeRow 12 ("012A3457698", 9), 33⟩, ⟨decodeRow 12 ("8012A345796", 9), 32⟩])
              (.leaf [⟨decodeRow 12 ("68012A34597", 11), 31⟩, ⟨decodeRow 12 ("8012A345967", 9), 32⟩, ⟨decodeRow 12 ("78012A34569", 11), 31⟩, ⟨decodeRow 12 ("8012A345679", 11), 32⟩, ⟨decodeRow 12 ("012A3456789", 11), 33⟩, ⟨decodeRow 12 ("12A34567809", 9), 34⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("912A3456708", 11), 33⟩, ⟨decodeRow 12 ("12A34567098", 9), 34⟩, ⟨decodeRow 12 ("812A3456790", 9), 33⟩, ⟨decodeRow 12 ("0812A345697", 11), 32⟩, ⟨decodeRow 12 ("812A3456907", 9), 33⟩])
              (.leaf [⟨decodeRow 12 ("7812A345609", 11), 32⟩, ⟨decodeRow 12 ("812A3456079", 11), 33⟩, ⟨decodeRow 12 ("12A34560789", 11), 34⟩, ⟨decodeRow 12 ("2A345607819", 9), 35⟩, ⟨decodeRow 12 ("92A34560718", 11), 34⟩, ⟨decodeRow 12 ("2A345607198", 9), 35⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("82A34560791", 9), 34⟩, ⟨decodeRow 12 ("182A3456097", 11), 33⟩, ⟨decodeRow 12 ("82A34560917", 9), 34⟩, ⟨decodeRow 12 ("782A3456019", 11), 33⟩, ⟨decodeRow 12 ("82A34560179", 11), 34⟩, ⟨decodeRow 12 ("2A345601789", 11), 35⟩])
              (.leaf [⟨decodeRow 12 ("A3456017829", 11), 36⟩, ⟨decodeRow 12 ("345601782A9", 9), 37⟩, ⟨decodeRow 12 ("934560178A2", 11), 36⟩, ⟨decodeRow 12 ("34560178A92", 9), 37⟩, ⟨decodeRow 12 ("2345601789A", 9), 36⟩, ⟨decodeRow 12 ("A2345601798", 9), 35⟩])))))
      (.branch 44
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("8A234560197", 11), 34⟩, ⟨decodeRow 12 ("A2345601987", 9), 35⟩, ⟨decodeRow 12 ("7A234560189", 11), 34⟩, ⟨decodeRow 12 ("A2345601879", 11), 35⟩, ⟨decodeRow 12 ("234560187A9", 9), 36⟩])
              (.leaf [⟨decodeRow 12 ("923456018A7", 11), 35⟩, ⟨decodeRow 12 ("23456018A97", 9), 36⟩, ⟨decodeRow 12 ("7234560189A", 9), 35⟩, ⟨decodeRow 12 ("A7234560198", 11), 34⟩, ⟨decodeRow 12 ("723456019A8", 9), 35⟩, ⟨decodeRow 12 ("872345601A9", 11), 34⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("72345601A89", 11), 35⟩, ⟨decodeRow 12 ("2345601A879", 9), 36⟩, ⟨decodeRow 12 ("92345601A78", 11), 35⟩, ⟨decodeRow 12 ("2345601A798", 9), 36⟩, ⟨decodeRow 12 ("82345601A97", 9), 35⟩])
              (.leaf [⟨decodeRow 12 ("7823456019A", 9), 34⟩, ⟨decodeRow 12 ("A7823456091", 11), 33⟩, ⟨decodeRow 12 ("782345609A1", 9), 34⟩, ⟨decodeRow 12 ("178234560A9", 11), 33⟩, ⟨decodeRow 12 ("78234560A19", 11), 34⟩, ⟨decodeRow 12 ("8234560A179", 11), 35⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("234560A1789", 11), 36⟩, ⟨decodeRow 12 ("34560A17829", 9), 37⟩, ⟨decodeRow 12 ("934560A1728", 11), 36⟩, ⟨decodeRow 12 ("34560A17298", 9), 37⟩, ⟨decodeRow 12 ("834560A1792", 9), 36⟩])
              (.leaf [⟨decodeRow 12 ("2834560A197", 11), 35⟩, ⟨decodeRow 12 ("834560A1927", 9), 36⟩, ⟨decodeRow 12 ("7834560A129", 11), 35⟩, ⟨decodeRow 12 ("834560A1279", 11), 36⟩, ⟨decodeRow 12 ("34560A12789", 11), 37⟩, ⟨decodeRow 12 ("4560A127839", 9), 38⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("94560A12738", 11), 37⟩, ⟨decodeRow 12 ("4560A127398", 9), 38⟩, ⟨decodeRow 12 ("84560A12793", 9), 37⟩, ⟨decodeRow 12 ("384560A1297", 11), 36⟩, ⟨decodeRow 12 ("84560A12937", 9), 37⟩])
              (.leaf [⟨decodeRow 12 ("784560A1239", 11), 36⟩, ⟨decodeRow 12 ("84560A12379", 11), 37⟩, ⟨decodeRow 12 ("4560A123789", 11), 38⟩, ⟨decodeRow 12 ("560A1237849", 9), 39⟩, ⟨decodeRow 12 ("9560A123748", 11), 38⟩, ⟨decodeRow 12 ("560A1237498", 9), 39⟩]))))
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("8560A123794", 9), 38⟩, ⟨decodeRow 12 ("48560A12397", 11), 37⟩, ⟨decodeRow 12 ("8560A123947", 9), 38⟩, ⟨decodeRow 12 ("78560A12349", 11), 37⟩, ⟨decodeRow 12 ("8560A123479", 11), 38⟩])
              (.leaf [⟨decodeRow 12 ("560A1234789", 11), 39⟩, ⟨decodeRow 12 ("60A12347859", 9), 40⟩, ⟨decodeRow 12 ("960A1234758", 11), 39⟩, ⟨decodeRow 12 ("60A12347598", 9), 40⟩, ⟨decodeRow 12 ("860A1234795", 9), 39⟩, ⟨decodeRow 12 ("5860A123497", 11), 38⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("860A1234957", 9), 39⟩, ⟨decodeRow 12 ("7860A123459", 11), 38⟩, ⟨decodeRow 12 ("860A1234579", 11), 39⟩, ⟨decodeRow 12 ("60A12345789", 11), 40⟩, ⟨decodeRow 12 ("0A123457869", 9), 41⟩])
              (.leaf [⟨decodeRow 12 ("90A12345768", 11), 40⟩, ⟨decodeRow 12 ("0A123457698", 9), 41⟩, ⟨decodeRow 12 ("80A12345796", 9), 40⟩, ⟨decodeRow 12 ("680A1234597", 11), 39⟩, ⟨decodeRow 12 ("80A12345967", 9), 40⟩, ⟨decodeRow 12 ("780A1234569", 11), 39⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("80A12345679", 11), 40⟩, ⟨decodeRow 12 ("0A123456789", 11), 41⟩, ⟨decodeRow 12 ("A1234567809", 11), 42⟩, ⟨decodeRow 12 ("123456780A9", 9), 43⟩, ⟨decodeRow 12 ("912345678A0", 9), 42⟩])
              (.leaf [⟨decodeRow 12 ("091234567A8", 11), 41⟩, ⟨decodeRow 12 ("91234567A08", 9), 42⟩, ⟨decodeRow 12 ("8912345670A", 11), 41⟩, ⟨decodeRow 12 ("9123456708A", 11), 42⟩, ⟨decodeRow 12 ("1234567089A", 9), 43⟩, ⟨decodeRow 12 ("A1234567098", 11), 42⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("123456709A8", 11), 43⟩, ⟨decodeRow 12 ("23456709A18", 9), 44⟩, ⟨decodeRow 12 ("8234567091A", 11), 43⟩, ⟨decodeRow 12 ("2345670918A", 11), 44⟩, ⟨decodeRow 12 ("3456709182A", 11), 45⟩, ⟨decodeRow 12 ("4567091823A", 11), 46⟩])
              (.leaf [⟨decodeRow 12 ("5670918234A", 11), 47⟩, ⟨decodeRow 12 ("6709182345A", 11), 48⟩, ⟨decodeRow 12 ("7091823456A", 11), 49⟩, ⟨decodeRow 12 ("0918234567A", 11), 50⟩, ⟨decodeRow 12 ("9182345670A", 9), 51⟩, ⟨decodeRow 12 ("A9182345607", 11), 50⟩]))))))
    (.branch 89
      (.branch 44
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("918234560A7", 11), 51⟩, ⟨decodeRow 12 ("18234560A97", 9), 52⟩, ⟨decodeRow 12 ("7182345609A", 11), 51⟩, ⟨decodeRow 12 ("1823456097A", 11), 52⟩, ⟨decodeRow 12 ("8234560971A", 9), 53⟩])
              (.leaf [⟨decodeRow 12 ("A8234560917", 9), 52⟩, ⟨decodeRow 12 ("7A823456019", 11), 51⟩, ⟨decodeRow 12 ("A8234560179", 11), 52⟩, ⟨decodeRow 12 ("823456017A9", 11), 53⟩, ⟨decodeRow 12 ("23456017A89", 11), 54⟩, ⟨decodeRow 12 ("3456017A829", 9), 55⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("93456017A28", 9), 54⟩, ⟨decodeRow 12 ("8934560172A", 11), 53⟩, ⟨decodeRow 12 ("9345601728A", 11), 54⟩, ⟨decodeRow 12 ("3456017289A", 9), 55⟩, ⟨decodeRow 12 ("A3456017298", 11), 54⟩])
              (.leaf [⟨decodeRow 12 ("345601729A8", 11), 55⟩, ⟨decodeRow 12 ("45601729A38", 9), 56⟩, ⟨decodeRow 12 ("8456017293A", 11), 55⟩, ⟨decodeRow 12 ("4560172938A", 11), 56⟩, ⟨decodeRow 12 ("5601729384A", 11), 57⟩, ⟨decodeRow 12 ("6017293845A", 11), 58⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("0172938456A", 11), 59⟩, ⟨decodeRow 12 ("1729384560A", 11), 60⟩, ⟨decodeRow 12 ("7293845601A", 11), 61⟩, ⟨decodeRow 12 ("2938456017A", 11), 62⟩, ⟨decodeRow 12 ("9384560172A", 9), 63⟩])
              (.leaf [⟨decodeRow 12 ("A9384560127", 11), 62⟩, ⟨decodeRow 12 ("938456012A7", 11), 63⟩, ⟨decodeRow 12 ("38456012A97", 9), 64⟩, ⟨decodeRow 12 ("7384560129A", 11), 63⟩, ⟨decodeRow 12 ("3845601297A", 11), 64⟩, ⟨decodeRow 12 ("8456012973A", 9), 65⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("A8456012937", 9), 64⟩, ⟨decodeRow 12 ("7A845601239", 11), 63⟩, ⟨decodeRow 12 ("A8456012379", 11), 64⟩, ⟨decodeRow 12 ("845601237A9", 11), 65⟩, ⟨decodeRow 12 ("45601237A89", 11), 66⟩])
              (.leaf [⟨decodeRow 12 ("5601237A849", 9), 67⟩, ⟨decodeRow 12 ("95601237A48", 9), 66⟩, ⟨decodeRow 12 ("8956012374A", 11), 65⟩, ⟨decodeRow 12 ("9560123748A", 11), 66⟩, ⟨decodeRow 12 ("5601237489A", 9), 67⟩, ⟨decodeRow 12 ("A5601237498", 11), 66⟩]))))
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("560123749A8", 11), 67⟩, ⟨decodeRow 12 ("60123749A58", 9), 68⟩, ⟨decodeRow 12 ("8601237495A", 11), 67⟩, ⟨decodeRow 12 ("6012374958A", 11), 68⟩, ⟨decodeRow 12 ("0123749586A", 11), 69⟩])
              (.leaf [⟨decodeRow 12 ("1237495860A", 11), 70⟩, ⟨decodeRow 12 ("2374958601A", 11), 71⟩, ⟨decodeRow 12 ("3749586012A", 11), 72⟩, ⟨decodeRow 12 ("7495860123A", 11), 73⟩, ⟨decodeRow 12 ("4958601237A", 11), 74⟩, ⟨decodeRow 12 ("9586012374A", 9), 75⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("A9586012347", 11), 74⟩, ⟨decodeRow 12 ("958601234A7", 11), 75⟩, ⟨decodeRow 12 ("58601234A97", 9), 76⟩, ⟨decodeRow 12 ("7586012349A", 11), 75⟩, ⟨decodeRow 12 ("5860123497A", 11), 76⟩])
              (.leaf [⟨decodeRow 12 ("8601234975A", 9), 77⟩, ⟨decodeRow 12 ("A8601234957", 9), 76⟩, ⟨decodeRow 12 ("7A860123459", 11), 75⟩, ⟨decodeRow 12 ("A8601234579", 11), 76⟩, ⟨decodeRow 12 ("860123457A9", 11), 77⟩, ⟨decodeRow 12 ("60123457A89", 11), 78⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("0123457A869", 9), 79⟩, ⟨decodeRow 12 ("90123457A68", 9), 78⟩, ⟨decodeRow 12 ("8901234576A", 11), 77⟩, ⟨decodeRow 12 ("9012345768A", 11), 78⟩, ⟨decodeRow 12 ("0123457689A", 9), 79⟩])
              (.leaf [⟨decodeRow 12 ("A0123457698", 11), 78⟩, ⟨decodeRow 12 ("012345769A8", 11), 79⟩, ⟨decodeRow 12 ("12345769A08", 9), 80⟩, ⟨decodeRow 12 ("8123457690A", 11), 79⟩, ⟨decodeRow 12 ("1234576908A", 11), 80⟩, ⟨decodeRow 12 ("2345769081A", 11), 81⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("3457690812A", 11), 82⟩, ⟨decodeRow 12 ("4576908123A", 11), 83⟩, ⟨decodeRow 12 ("5769081234A", 11), 84⟩, ⟨decodeRow 12 ("7690812345A", 11), 85⟩, ⟨decodeRow 12 ("6908123457A", 11), 86⟩, ⟨decodeRow 12 ("9081234576A", 9), 87⟩])
              (.leaf [⟨decodeRow 12 ("A9081234567", 11), 86⟩, ⟨decodeRow 12 ("908123456A7", 11), 87⟩, ⟨decodeRow 12 ("08123456A97", 9), 88⟩, ⟨decodeRow 12 ("7081234569A", 11), 87⟩, ⟨decodeRow 12 ("0812345697A", 11), 88⟩, ⟨decodeRow 12 ("8123456970A", 9), 89⟩])))))
      (.branch 45
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("A8123456907", 9), 88⟩, ⟨decodeRow 12 ("7A812345609", 11), 87⟩, ⟨decodeRow 12 ("A8123456079", 11), 88⟩, ⟨decodeRow 12 ("812345607A9", 11), 89⟩, ⟨decodeRow 12 ("12345607A89", 11), 90⟩])
              (.leaf [⟨decodeRow 12 ("2345607A819", 9), 91⟩, ⟨decodeRow 12 ("92345607A18", 9), 90⟩, ⟨decodeRow 12 ("8923456071A", 11), 89⟩, ⟨decodeRow 12 ("9234560718A", 11), 90⟩, ⟨decodeRow 12 ("2345607189A", 9), 91⟩, ⟨decodeRow 12 ("A2345607198", 11), 90⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("234560719A8", 11), 91⟩, ⟨decodeRow 12 ("34560719A28", 9), 92⟩, ⟨decodeRow 12 ("8345607192A", 11), 91⟩, ⟨decodeRow 12 ("3456071928A", 11), 92⟩, ⟨decodeRow 12 ("4560719283A", 11), 93⟩])
              (.leaf [⟨decodeRow 12 ("5607192834A", 11), 94⟩, ⟨decodeRow 12 ("6071928345A", 11), 95⟩, ⟨decodeRow 12 ("0719283456A", 11), 96⟩, ⟨decodeRow 12 ("7192834560A", 11), 97⟩, ⟨decodeRow 12 ("1928345607A", 11), 98⟩, ⟨decodeRow 12 ("9283456071A", 9), 99⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("A9283456017", 11), 98⟩, ⟨decodeRow 12 ("928345601A7", 11), 99⟩, ⟨decodeRow 12 ("28345601A97", 9), 100⟩, ⟨decodeRow 12 ("7283456019A", 11), 99⟩, ⟨decodeRow 12 ("2834560197A", 11), 100⟩])
              (.leaf [⟨decodeRow 12 ("8345601972A", 9), 101⟩, ⟨decodeRow 12 ("A8345601927", 9), 100⟩, ⟨decodeRow 12 ("7A834560129", 11), 99⟩, ⟨decodeRow 12 ("A8345601279", 11), 100⟩, ⟨decodeRow 12 ("834560127A9", 11), 101⟩, ⟨decodeRow 12 ("34560127A89", 11), 102⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("4560127A839", 9), 103⟩, ⟨decodeRow 12 ("94560127A38", 9), 102⟩, ⟨decodeRow 12 ("8945601273A", 11), 101⟩, ⟨decodeRow 12 ("9456012738A", 11), 102⟩, ⟨decodeRow 12 ("4560127389A", 9), 103⟩, ⟨decodeRow 12 ("A4560127398", 11), 102⟩])
              (.leaf [⟨decodeRow 12 ("456012739A8", 11), 103⟩, ⟨decodeRow 12 ("56012739A48", 9), 104⟩, ⟨decodeRow 12 ("8560127394A", 11), 103⟩, ⟨decodeRow 12 ("5601273948A", 11), 104⟩, ⟨decodeRow 12 ("6012739485A", 11), 105⟩, ⟨decodeRow 12 ("0127394856A", 11), 106⟩]))))
        (.branch 22
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("1273948560A", 11), 107⟩, ⟨decodeRow 12 ("2739485601A", 11), 108⟩, ⟨decodeRow 12 ("7394856012A", 11), 109⟩, ⟨decodeRow 12 ("3948560127A", 11), 110⟩, ⟨decodeRow 12 ("9485601273A", 9), 111⟩])
              (.leaf [⟨decodeRow 12 ("A9485601237", 11), 110⟩, ⟨decodeRow 12 ("948560123A7", 11), 111⟩, ⟨decodeRow 12 ("48560123A97", 9), 112⟩, ⟨decodeRow 12 ("7485601239A", 11), 111⟩, ⟨decodeRow 12 ("4856012397A", 11), 112⟩, ⟨decodeRow 12 ("8560123974A", 9), 113⟩]))
            (.branch 5
              (.leaf [⟨decodeRow 12 ("A8560123947", 9), 112⟩, ⟨decodeRow 12 ("7A856012349", 11), 111⟩, ⟨decodeRow 12 ("A8560123479", 11), 112⟩, ⟨decodeRow 12 ("856012347A9", 11), 113⟩, ⟨decodeRow 12 ("56012347A89", 11), 114⟩])
              (.leaf [⟨decodeRow 12 ("6012347A859", 9), 115⟩, ⟨decodeRow 12 ("96012347A58", 9), 114⟩, ⟨decodeRow 12 ("8960123475A", 11), 113⟩, ⟨decodeRow 12 ("9601234758A", 11), 114⟩, ⟨decodeRow 12 ("6012347589A", 9), 115⟩, ⟨decodeRow 12 ("A6012347598", 11), 114⟩])))
          (.branch 11
            (.branch 5
              (.leaf [⟨decodeRow 12 ("601234759A8", 11), 115⟩, ⟨decodeRow 12 ("01234759A68", 9), 116⟩, ⟨decodeRow 12 ("8012347596A", 11), 115⟩, ⟨decodeRow 12 ("0123475968A", 11), 116⟩, ⟨decodeRow 12 ("1234759680A", 11), 117⟩])
              (.leaf [⟨decodeRow 12 ("2347596801A", 11), 118⟩, ⟨decodeRow 12 ("3475968012A", 11), 119⟩, ⟨decodeRow 12 ("4759680123A", 11), 120⟩, ⟨decodeRow 12 ("7596801234A", 11), 121⟩, ⟨decodeRow 12 ("5968012347A", 11), 122⟩, ⟨decodeRow 12 ("9680123475A", 9), 123⟩]))
            (.branch 6
              (.leaf [⟨decodeRow 12 ("A9680123457", 11), 122⟩, ⟨decodeRow 12 ("968012345A7", 11), 123⟩, ⟨decodeRow 12 ("68012345A97", 9), 124⟩, ⟨decodeRow 12 ("7680123459A", 11), 123⟩, ⟨decodeRow 12 ("6801234597A", 11), 124⟩, ⟨decodeRow 12 ("8012345976A", 9), 125⟩])
              (.leaf [⟨decodeRow 12 ("A8012345967", 9), 124⟩, ⟨decodeRow 12 ("7A801234569", 11), 123⟩, ⟨decodeRow 12 ("A8012345679", 11), 124⟩, ⟨decodeRow 12 ("801234567A9", 11), 125⟩, ⟨decodeRow 12 ("01234567A89", 9), 126⟩, ⟨decodeRow 12 ("9012345678A", 11), 125⟩])))))))

theorem rows_eq : tree.flatten.map Point.row = BlockF0.rows := by rfl

theorem excesses_eq : tree.flatten.map Point.excess = BlockF0.prefixes := by rfl

noncomputable def point (i : Nat) : Option Point := tree.get? i

theorem point_sound (i : Nat) {p : Point} (hp : point i = some p) :
    p.Occurs BlockF0.rows :=
  PointTree.get_sound tree BlockF0.rows BlockF0.prefixes rows_eq excesses_eq
    BlockF0.prefixes_checked i hp

end SuperpermutationUpperBound.Native14.Pointers.FastBlockF0
