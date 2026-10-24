module

public import upper.pointers.PointTree
public import upper.certificate.BlockF2Prefixes

@[expose] public section

/-! Balanced source-point data. Both projections are kernel checked once;
lookup soundness then follows from literal membership in this tree. -/
namespace SuperpermutationUpperBound.Native14.Pointers.FastBlockF2
open Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

noncomputable def tree : PointTree :=
  .branch 1015
  (.branch 507
    (.branch 253
      (.branch 126
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("9A012347568", 11), 0⟩, ⟨decodeRow 12 ("A0123475698", 11), 1⟩, ⟨decodeRow 12 ("012347569A8", 11), 2⟩, ⟨decodeRow 12 ("12347569A08", 9), 3⟩, ⟨decodeRow 12 ("8123475690A", 9), 2⟩, ⟨decodeRow 12 ("A8123475609", 11), 1⟩, ⟨decodeRow 12 ("812347560A9", 11), 2⟩])
                (.leaf [⟨decodeRow 12 ("12347560A89", 11), 3⟩, ⟨decodeRow 12 ("2347560A819", 11), 4⟩, ⟨decodeRow 12 ("347560A8129", 11), 5⟩, ⟨decodeRow 12 ("47560A81239", 11), 6⟩, ⟨decodeRow 12 ("7560A812349", 11), 7⟩, ⟨decodeRow 12 ("560A8123479", 11), 8⟩, ⟨decodeRow 12 ("60A81234759", 9), 9⟩, ⟨decodeRow 12 ("960A8123457", 11), 8⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("60A81234597", 11), 9⟩, ⟨decodeRow 12 ("0A812345967", 11), 10⟩, ⟨decodeRow 12 ("A8123459607", 11), 11⟩, ⟨decodeRow 12 ("812345960A7", 11), 12⟩, ⟨decodeRow 12 ("12345960A87", 11), 13⟩, ⟨decodeRow 12 ("2345960A817", 9), 14⟩, ⟨decodeRow 12 ("72345960A18", 11), 13⟩, ⟨decodeRow 12 ("2345960A178", 9), 14⟩])
                (.leaf [⟨decodeRow 12 ("82345960A71", 9), 13⟩, ⟨decodeRow 12 ("1823459607A", 11), 12⟩, ⟨decodeRow 12 ("8234596071A", 11), 13⟩, ⟨decodeRow 12 ("2345960718A", 11), 14⟩, ⟨decodeRow 12 ("3459607182A", 9), 15⟩, ⟨decodeRow 12 ("A3459607128", 11), 14⟩, ⟨decodeRow 12 ("345960712A8", 9), 15⟩, ⟨decodeRow 12 ("834596071A2", 9), 14⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("283459607A1", 9), 13⟩, ⟨decodeRow 12 ("128345960A7", 11), 12⟩, ⟨decodeRow 12 ("28345960A17", 11), 13⟩, ⟨decodeRow 12 ("8345960A127", 11), 14⟩, ⟨decodeRow 12 ("345960A1287", 11), 15⟩, ⟨decodeRow 12 ("45960A12837", 9), 16⟩, ⟨decodeRow 12 ("745960A1238", 11), 15⟩, ⟨decodeRow 12 ("45960A12378", 11), 16⟩])
                (.leaf [⟨decodeRow 12 ("5960A123748", 11), 17⟩, ⟨decodeRow 12 ("960A1237458", 11), 18⟩, ⟨decodeRow 12 ("60A12374598", 11), 19⟩, ⟨decodeRow 12 ("0A123745968", 9), 20⟩, ⟨decodeRow 12 ("80A12374569", 11), 19⟩, ⟨decodeRow 12 ("0A123745689", 11), 20⟩, ⟨decodeRow 12 ("A1237456809", 11), 21⟩, ⟨decodeRow 12 ("123745680A9", 11), 22⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("23745680A19", 11), 23⟩, ⟨decodeRow 12 ("3745680A129", 11), 24⟩, ⟨decodeRow 12 ("745680A1239", 11), 25⟩, ⟨decodeRow 12 ("45680A12379", 11), 26⟩, ⟨decodeRow 12 ("5680A123749", 9), 27⟩, ⟨decodeRow 12 ("95680A12347", 11), 26⟩, ⟨decodeRow 12 ("5680A123497", 11), 27⟩, ⟨decodeRow 12 ("680A1234957", 11), 28⟩])
                (.leaf [⟨decodeRow 12 ("80A12349567", 11), 29⟩, ⟨decodeRow 12 ("0A123495687", 11), 30⟩, ⟨decodeRow 12 ("A1234956807", 9), 31⟩, ⟨decodeRow 12 ("7A123495608", 11), 30⟩, ⟨decodeRow 12 ("A1234956078", 11), 31⟩, ⟨decodeRow 12 ("123495607A8", 11), 32⟩, ⟨decodeRow 12 ("23495607A18", 9), 33⟩, ⟨decodeRow 12 ("8234956071A", 9), 32⟩]))))
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("A8234956017", 11), 31⟩, ⟨decodeRow 12 ("823495601A7", 11), 32⟩, ⟨decodeRow 12 ("23495601A87", 11), 33⟩, ⟨decodeRow 12 ("3495601A827", 9), 34⟩, ⟨decodeRow 12 ("73495601A28", 11), 33⟩, ⟨decodeRow 12 ("3495601A278", 11), 34⟩, ⟨decodeRow 12 ("495601A2738", 11), 35⟩])
                (.leaf [⟨decodeRow 12 ("95601A27348", 11), 36⟩, ⟨decodeRow 12 ("5601A273498", 11), 37⟩, ⟨decodeRow 12 ("601A2734958", 9), 38⟩, ⟨decodeRow 12 ("8601A273459", 11), 37⟩, ⟨decodeRow 12 ("601A2734589", 11), 38⟩, ⟨decodeRow 12 ("01A27345869", 11), 39⟩, ⟨decodeRow 12 ("1A273458609", 11), 40⟩, ⟨decodeRow 12 ("A2734586019", 11), 41⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("273458601A9", 11), 42⟩, ⟨decodeRow 12 ("73458601A29", 11), 43⟩, ⟨decodeRow 12 ("3458601A279", 11), 44⟩, ⟨decodeRow 12 ("458601A2739", 9), 45⟩, ⟨decodeRow 12 ("9458601A237", 11), 44⟩, ⟨decodeRow 12 ("458601A2397", 11), 45⟩, ⟨decodeRow 12 ("58601A23947", 11), 46⟩, ⟨decodeRow 12 ("8601A239457", 11), 47⟩])
                (.leaf [⟨decodeRow 12 ("601A2394587", 11), 48⟩, ⟨decodeRow 12 ("01A23945867", 9), 49⟩, ⟨decodeRow 12 ("701A2394568", 11), 48⟩, ⟨decodeRow 12 ("01A23945678", 11), 49⟩, ⟨decodeRow 12 ("1A239456708", 11), 50⟩, ⟨decodeRow 12 ("A2394567018", 11), 51⟩, ⟨decodeRow 12 ("239456701A8", 9), 52⟩, ⟨decodeRow 12 ("823945670A1", 9), 51⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("182394567A0", 9), 50⟩, ⟨decodeRow 12 ("018239456A7", 11), 49⟩, ⟨decodeRow 12 ("18239456A07", 9), 50⟩, ⟨decodeRow 12 ("7182394560A", 11), 49⟩, ⟨decodeRow 12 ("1823945607A", 11), 50⟩, ⟨decodeRow 12 ("8239456071A", 11), 51⟩, ⟨decodeRow 12 ("2394560718A", 9), 52⟩, ⟨decodeRow 12 ("A2394560781", 9), 51⟩])
                (.leaf [⟨decodeRow 12 ("1A239456087", 11), 50⟩, ⟨decodeRow 12 ("A2394560817", 9), 51⟩, ⟨decodeRow 12 ("7A239456018", 11), 50⟩, ⟨decodeRow 12 ("A2394560178", 11), 51⟩, ⟨decodeRow 12 ("239456017A8", 11), 52⟩, ⟨decodeRow 12 ("39456017A28", 11), 53⟩, ⟨decodeRow 12 ("9456017A238", 11), 54⟩, ⟨decodeRow 12 ("456017A2398", 11), 55⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("56017A23948", 9), 56⟩, ⟨decodeRow 12 ("856017A2349", 11), 55⟩, ⟨decodeRow 12 ("56017A23489", 11), 56⟩, ⟨decodeRow 12 ("6017A234859", 11), 57⟩, ⟨decodeRow 12 ("017A2348569", 11), 58⟩, ⟨decodeRow 12 ("17A23485609", 11), 59⟩, ⟨decodeRow 12 ("7A234856019", 11), 60⟩, ⟨decodeRow 12 ("A2348560179", 11), 61⟩])
                (.leaf [⟨decodeRow 12 ("234856017A9", 11), 62⟩, ⟨decodeRow 12 ("34856017A29", 9), 63⟩, ⟨decodeRow 12 ("9348560172A", 9), 62⟩, ⟨decodeRow 12 ("A9348560127", 11), 61⟩, ⟨decodeRow 12 ("934856012A7", 11), 62⟩, ⟨decodeRow 12 ("34856012A97", 11), 63⟩, ⟨decodeRow 12 ("4856012A937", 11), 64⟩, ⟨decodeRow 12 ("856012A9347", 11), 65⟩])))))
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("56012A93487", 11), 66⟩, ⟨decodeRow 12 ("6012A934857", 9), 67⟩, ⟨decodeRow 12 ("76012A93458", 11), 66⟩, ⟨decodeRow 12 ("6012A934578", 11), 67⟩, ⟨decodeRow 12 ("012A9345768", 9), 68⟩, ⟨decodeRow 12 ("8012A934567", 11), 67⟩, ⟨decodeRow 12 ("012A9345687", 11), 68⟩])
                (.leaf [⟨decodeRow 12 ("12A93456807", 9), 69⟩, ⟨decodeRow 12 ("712A9345608", 11), 68⟩, ⟨decodeRow 12 ("12A93456078", 11), 69⟩, ⟨decodeRow 12 ("2A934560718", 11), 70⟩, ⟨decodeRow 12 ("A9345607128", 11), 71⟩, ⟨decodeRow 12 ("934560712A8", 11), 72⟩, ⟨decodeRow 12 ("34560712A98", 11), 73⟩, ⟨decodeRow 12 ("4560712A938", 9), 74⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("84560712A39", 11), 73⟩, ⟨decodeRow 12 ("4560712A389", 11), 74⟩, ⟨decodeRow 12 ("560712A3849", 11), 75⟩, ⟨decodeRow 12 ("60712A38459", 11), 76⟩, ⟨decodeRow 12 ("0712A384569", 11), 77⟩, ⟨decodeRow 12 ("712A3845609", 11), 78⟩, ⟨decodeRow 12 ("12A38456079", 11), 79⟩, ⟨decodeRow 12 ("2A384560719", 9), 80⟩])
                (.leaf [⟨decodeRow 12 ("92A38456017", 11), 79⟩, ⟨decodeRow 12 ("2A384560197", 11), 80⟩, ⟨decodeRow 12 ("A3845601927", 11), 81⟩, ⟨decodeRow 12 ("384560192A7", 11), 82⟩, ⟨decodeRow 12 ("84560192A37", 11), 83⟩, ⟨decodeRow 12 ("4560192A387", 11), 84⟩, ⟨decodeRow 12 ("560192A3847", 9), 85⟩, ⟨decodeRow 12 ("7560192A348", 11), 84⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("560192A3478", 11), 85⟩, ⟨decodeRow 12 ("60192A34758", 9), 86⟩, ⟨decodeRow 12 ("860192A3457", 11), 85⟩, ⟨decodeRow 12 ("60192A34587", 11), 86⟩, ⟨decodeRow 12 ("0192A345867", 9), 87⟩, ⟨decodeRow 12 ("70192A34568", 11), 86⟩, ⟨decodeRow 12 ("0192A345678", 11), 87⟩, ⟨decodeRow 12 ("192A3456708", 11), 88⟩])
                (.leaf [⟨decodeRow 12 ("92A34567018", 11), 89⟩, ⟨decodeRow 12 ("2A345670198", 11), 90⟩, ⟨decodeRow 12 ("A3456701928", 9), 91⟩, ⟨decodeRow 12 ("8A345670129", 11), 90⟩, ⟨decodeRow 12 ("A3456701289", 11), 91⟩, ⟨decodeRow 12 ("345670128A9", 11), 92⟩, ⟨decodeRow 12 ("45670128A39", 11), 93⟩, ⟨decodeRow 12 ("5670128A349", 11), 94⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("670128A3459", 11), 95⟩, ⟨decodeRow 12 ("70128A34569", 11), 96⟩, ⟨decodeRow 12 ("0128A345679", 11), 97⟩, ⟨decodeRow 12 ("128A3456709", 9), 98⟩, ⟨decodeRow 12 ("9128A345607", 11), 97⟩, ⟨decodeRow 12 ("128A3456097", 11), 98⟩, ⟨decodeRow 12 ("28A34560917", 11), 99⟩, ⟨decodeRow 12 ("8A345609127", 11), 100⟩])
                (.leaf [⟨decodeRow 12 ("A3456091287", 11), 101⟩, ⟨decodeRow 12 ("345609128A7", 11), 102⟩, ⟨decodeRow 12 ("45609128A37", 9), 103⟩, ⟨decodeRow 12 ("7456091283A", 9), 102⟩, ⟨decodeRow 12 ("A7456091238", 11), 101⟩, ⟨decodeRow 12 ("745609123A8", 11), 102⟩, ⟨decodeRow 12 ("45609123A78", 11), 103⟩, ⟨decodeRow 12 ("5609123A748", 9), 104⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("85609123A47", 11), 103⟩, ⟨decodeRow 12 ("5609123A487", 9), 104⟩, ⟨decodeRow 12 ("75609123A84", 9), 103⟩, ⟨decodeRow 12 ("4756091238A", 11), 102⟩, ⟨decodeRow 12 ("7560912384A", 11), 103⟩, ⟨decodeRow 12 ("5609123847A", 11), 104⟩, ⟨decodeRow 12 ("6091238475A", 9), 105⟩, ⟨decodeRow 12 ("A6091238457", 11), 104⟩])
                (.leaf [⟨decodeRow 12 ("609123845A7", 9), 105⟩, ⟨decodeRow 12 ("760912384A5", 9), 104⟩, ⟨decodeRow 12 ("576091238A4", 9), 103⟩, ⟨decodeRow 12 ("457609123A8", 11), 102⟩, ⟨decodeRow 12 ("57609123A48", 11), 103⟩, ⟨decodeRow 12 ("7609123A458", 11), 104⟩, ⟨decodeRow 12 ("609123A4578", 11), 105⟩, ⟨decodeRow 12 ("09123A45768", 11), 106⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("9123A457608", 11), 107⟩, ⟨decodeRow 12 ("123A4576098", 11), 108⟩, ⟨decodeRow 12 ("23A45760918", 9), 109⟩, ⟨decodeRow 12 ("823A4576019", 11), 108⟩, ⟨decodeRow 12 ("23A45760189", 11), 109⟩, ⟨decodeRow 12 ("3A457601829", 11), 110⟩, ⟨decodeRow 12 ("A4576018239", 11), 111⟩, ⟨decodeRow 12 ("457601823A9", 11), 112⟩])
                (.leaf [⟨decodeRow 12 ("57601823A49", 11), 113⟩, ⟨decodeRow 12 ("7601823A459", 11), 114⟩, ⟨decodeRow 12 ("601823A4579", 11), 115⟩, ⟨decodeRow 12 ("01823A45769", 9), 116⟩, ⟨decodeRow 12 ("901823A4567", 11), 115⟩, ⟨decodeRow 12 ("01823A45697", 11), 116⟩, ⟨decodeRow 12 ("1823A456907", 11), 117⟩, ⟨decodeRow 12 ("823A4569017", 11), 118⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("23A45690187", 11), 119⟩, ⟨decodeRow 12 ("3A456901827", 9), 120⟩, ⟨decodeRow 12 ("73A45690128", 11), 119⟩, ⟨decodeRow 12 ("3A456901278", 11), 120⟩, ⟨decodeRow 12 ("A4569012738", 9), 121⟩, ⟨decodeRow 12 ("8A456901237", 11), 120⟩, ⟨decodeRow 12 ("A4569012387", 11), 121⟩, ⟨decodeRow 12 ("456901238A7", 11), 122⟩])
                (.leaf [⟨decodeRow 12 ("56901238A47", 9), 123⟩, ⟨decodeRow 12 ("7569012384A", 9), 122⟩, ⟨decodeRow 12 ("A7569012348", 11), 121⟩, ⟨decodeRow 12 ("756901234A8", 11), 122⟩, ⟨decodeRow 12 ("56901234A78", 11), 123⟩, ⟨decodeRow 12 ("6901234A758", 11), 124⟩, ⟨decodeRow 12 ("901234A7568", 11), 125⟩, ⟨decodeRow 12 ("01234A75698", 11), 126⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("1234A756908", 9), 127⟩, ⟨decodeRow 12 ("81234A75609", 11), 126⟩, ⟨decodeRow 12 ("1234A756089", 11), 127⟩, ⟨decodeRow 12 ("234A7560819", 11), 128⟩, ⟨decodeRow 12 ("34A75608129", 11), 129⟩, ⟨decodeRow 12 ("4A756081239", 11), 130⟩, ⟨decodeRow 12 ("A7560812349", 11), 131⟩, ⟨decodeRow 12 ("756081234A9", 11), 132⟩])
                (.leaf [⟨decodeRow 12 ("56081234A79", 11), 133⟩, ⟨decodeRow 12 ("6081234A759", 9), 134⟩, ⟨decodeRow 12 ("96081234A57", 11), 133⟩, ⟨decodeRow 12 ("6081234A597", 11), 134⟩, ⟨decodeRow 12 ("081234A5967", 11), 135⟩, ⟨decodeRow 12 ("81234A59607", 11), 136⟩, ⟨decodeRow 12 ("1234A596087", 11), 137⟩, ⟨decodeRow 12 ("234A5960817", 9), 138⟩]))))))
      (.branch 127
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("7234A596018", 11), 137⟩, ⟨decodeRow 12 ("234A5960178", 11), 138⟩, ⟨decodeRow 12 ("34A59601728", 9), 139⟩, ⟨decodeRow 12 ("834A5960127", 11), 138⟩, ⟨decodeRow 12 ("34A59601287", 11), 139⟩, ⟨decodeRow 12 ("4A596012837", 9), 140⟩, ⟨decodeRow 12 ("74A59601238", 11), 139⟩])
                (.leaf [⟨decodeRow 12 ("4A596012378", 11), 140⟩, ⟨decodeRow 12 ("A5960123748", 11), 141⟩, ⟨decodeRow 12 ("596012374A8", 11), 142⟩, ⟨decodeRow 12 ("96012374A58", 11), 143⟩, ⟨decodeRow 12 ("6012374A598", 11), 144⟩, ⟨decodeRow 12 ("012374A5968", 9), 145⟩, ⟨decodeRow 12 ("8012374A569", 11), 144⟩, ⟨decodeRow 12 ("012374A5689", 11), 145⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("12374A56809", 11), 146⟩, ⟨decodeRow 12 ("2374A568019", 11), 147⟩, ⟨decodeRow 12 ("374A5680129", 11), 148⟩, ⟨decodeRow 12 ("74A56801239", 11), 149⟩, ⟨decodeRow 12 ("4A568012379", 11), 150⟩, ⟨decodeRow 12 ("A5680123749", 9), 151⟩, ⟨decodeRow 12 ("9A568012347", 11), 150⟩, ⟨decodeRow 12 ("A5680123497", 11), 151⟩])
                (.leaf [⟨decodeRow 12 ("568012349A7", 11), 152⟩, ⟨decodeRow 12 ("68012349A57", 11), 153⟩, ⟨decodeRow 12 ("8012349A567", 11), 154⟩, ⟨decodeRow 12 ("012349A5687", 11), 155⟩, ⟨decodeRow 12 ("12349A56807", 9), 156⟩, ⟨decodeRow 12 ("712349A5608", 11), 155⟩, ⟨decodeRow 12 ("12349A56078", 11), 156⟩, ⟨decodeRow 12 ("2349A560718", 9), 157⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("82349A56017", 11), 156⟩, ⟨decodeRow 12 ("2349A560187", 11), 157⟩, ⟨decodeRow 12 ("349A5601827", 9), 158⟩, ⟨decodeRow 12 ("7349A560128", 11), 157⟩, ⟨decodeRow 12 ("349A5601278", 11), 158⟩, ⟨decodeRow 12 ("49A56012738", 11), 159⟩, ⟨decodeRow 12 ("9A560127348", 11), 160⟩, ⟨decodeRow 12 ("A5601273498", 11), 161⟩])
                (.leaf [⟨decodeRow 12 ("560127349A8", 11), 162⟩, ⟨decodeRow 12 ("60127349A58", 9), 163⟩, ⟨decodeRow 12 ("8601273495A", 9), 162⟩, ⟨decodeRow 12 ("A8601273459", 11), 161⟩, ⟨decodeRow 12 ("860127345A9", 11), 162⟩, ⟨decodeRow 12 ("60127345A89", 11), 163⟩, ⟨decodeRow 12 ("0127345A869", 11), 164⟩, ⟨decodeRow 12 ("127345A8609", 11), 165⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("27345A86019", 11), 166⟩, ⟨decodeRow 12 ("7345A860129", 11), 167⟩, ⟨decodeRow 12 ("345A8601279", 11), 168⟩, ⟨decodeRow 12 ("45A86012739", 9), 169⟩, ⟨decodeRow 12 ("945A8601237", 11), 168⟩, ⟨decodeRow 12 ("45A86012397", 11), 169⟩, ⟨decodeRow 12 ("5A860123947", 11), 170⟩, ⟨decodeRow 12 ("A8601239457", 11), 171⟩])
                (.leaf [⟨decodeRow 12 ("860123945A7", 11), 172⟩, ⟨decodeRow 12 ("60123945A87", 11), 173⟩, ⟨decodeRow 12 ("0123945A867", 9), 174⟩, ⟨decodeRow 12 ("70123945A68", 11), 173⟩, ⟨decodeRow 12 ("0123945A678", 9), 174⟩, ⟨decodeRow 12 ("80123945A76", 9), 173⟩, ⟨decodeRow 12 ("6801239457A", 11), 172⟩, ⟨decodeRow 12 ("8012394576A", 11), 173⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("0123945768A", 11), 174⟩, ⟨decodeRow 12 ("1239457680A", 9), 175⟩, ⟨decodeRow 12 ("A1239457608", 11), 174⟩, ⟨decodeRow 12 ("123945760A8", 9), 175⟩, ⟨decodeRow 12 ("812394576A0", 9), 174⟩, ⟨decodeRow 12 ("081239457A6", 9), 173⟩, ⟨decodeRow 12 ("608123945A7", 11), 172⟩, ⟨decodeRow 12 ("08123945A67", 11), 173⟩])
                (.leaf [⟨decodeRow 12 ("8123945A607", 11), 174⟩, ⟨decodeRow 12 ("123945A6087", 11), 175⟩, ⟨decodeRow 12 ("23945A60817", 9), 176⟩, ⟨decodeRow 12 ("723945A6018", 11), 175⟩, ⟨decodeRow 12 ("23945A60178", 11), 176⟩, ⟨decodeRow 12 ("3945A601728", 11), 177⟩, ⟨decodeRow 12 ("945A6017238", 11), 178⟩, ⟨decodeRow 12 ("45A60172398", 11), 179⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("5A601723948", 9), 180⟩, ⟨decodeRow 12 ("85A60172349", 11), 179⟩, ⟨decodeRow 12 ("5A601723489", 11), 180⟩, ⟨decodeRow 12 ("A6017234859", 11), 181⟩, ⟨decodeRow 12 ("601723485A9", 11), 182⟩, ⟨decodeRow 12 ("01723485A69", 11), 183⟩, ⟨decodeRow 12 ("1723485A609", 11), 184⟩, ⟨decodeRow 12 ("723485A6019", 11), 185⟩])
                (.leaf [⟨decodeRow 12 ("23485A60179", 11), 186⟩, ⟨decodeRow 12 ("3485A601729", 9), 187⟩, ⟨decodeRow 12 ("93485A60127", 11), 186⟩, ⟨decodeRow 12 ("3485A601297", 11), 187⟩, ⟨decodeRow 12 ("485A6012937", 11), 188⟩, ⟨decodeRow 12 ("85A60129347", 11), 189⟩, ⟨decodeRow 12 ("5A601293487", 11), 190⟩, ⟨decodeRow 12 ("A6012934857", 9), 191⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("7A601293458", 11), 190⟩, ⟨decodeRow 12 ("A6012934578", 11), 191⟩, ⟨decodeRow 12 ("601293457A8", 11), 192⟩, ⟨decodeRow 12 ("01293457A68", 9), 193⟩, ⟨decodeRow 12 ("8012934576A", 9), 192⟩, ⟨decodeRow 12 ("A8012934567", 11), 191⟩, ⟨decodeRow 12 ("801293456A7", 11), 192⟩, ⟨decodeRow 12 ("01293456A87", 11), 193⟩])
                (.leaf [⟨decodeRow 12 ("1293456A807", 9), 194⟩, ⟨decodeRow 12 ("71293456A08", 11), 193⟩, ⟨decodeRow 12 ("1293456A078", 11), 194⟩, ⟨decodeRow 12 ("293456A0718", 11), 195⟩, ⟨decodeRow 12 ("93456A07128", 11), 196⟩, ⟨decodeRow 12 ("3456A071298", 11), 197⟩, ⟨decodeRow 12 ("456A0712938", 9), 198⟩, ⟨decodeRow 12 ("8456A071239", 11), 197⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("456A0712389", 11), 198⟩, ⟨decodeRow 12 ("56A07123849", 11), 199⟩, ⟨decodeRow 12 ("6A071238459", 11), 200⟩, ⟨decodeRow 12 ("A0712384569", 11), 201⟩, ⟨decodeRow 12 ("071238456A9", 11), 202⟩, ⟨decodeRow 12 ("71238456A09", 11), 203⟩, ⟨decodeRow 12 ("1238456A079", 11), 204⟩, ⟨decodeRow 12 ("238456A0719", 9), 205⟩])
                (.leaf [⟨decodeRow 12 ("9238456A017", 11), 204⟩, ⟨decodeRow 12 ("238456A0197", 11), 205⟩, ⟨decodeRow 12 ("38456A01927", 11), 206⟩, ⟨decodeRow 12 ("8456A019237", 11), 207⟩, ⟨decodeRow 12 ("456A0192387", 11), 208⟩, ⟨decodeRow 12 ("56A01923847", 9), 209⟩, ⟨decodeRow 12 ("756A0192348", 11), 208⟩, ⟨decodeRow 12 ("56A01923478", 11), 209⟩])))))
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("6A019234758", 11), 210⟩, ⟨decodeRow 12 ("A0192347568", 11), 211⟩, ⟨decodeRow 12 ("019234756A8", 9), 212⟩, ⟨decodeRow 12 ("801923475A6", 9), 211⟩, ⟨decodeRow 12 ("680192347A5", 9), 210⟩, ⟨decodeRow 12 ("568019234A7", 11), 209⟩, ⟨decodeRow 12 ("68019234A57", 9), 210⟩])
                (.leaf [⟨decodeRow 12 ("7680192345A", 11), 209⟩, ⟨decodeRow 12 ("6801923457A", 11), 210⟩, ⟨decodeRow 12 ("8019234576A", 11), 211⟩, ⟨decodeRow 12 ("0192345768A", 9), 212⟩, ⟨decodeRow 12 ("A0192345786", 9), 211⟩, ⟨decodeRow 12 ("6A019234587", 11), 210⟩, ⟨decodeRow 12 ("A0192345867", 9), 211⟩, ⟨decodeRow 12 ("7A019234568", 11), 210⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A0192345678", 11), 211⟩, ⟨decodeRow 12 ("019234567A8", 11), 212⟩, ⟨decodeRow 12 ("19234567A08", 11), 213⟩, ⟨decodeRow 12 ("9234567A018", 11), 214⟩, ⟨decodeRow 12 ("234567A0198", 11), 215⟩, ⟨decodeRow 12 ("34567A01928", 9), 216⟩, ⟨decodeRow 12 ("834567A0129", 11), 215⟩, ⟨decodeRow 12 ("34567A01289", 11), 216⟩])
                (.leaf [⟨decodeRow 12 ("4567A012839", 11), 217⟩, ⟨decodeRow 12 ("567A0128349", 11), 218⟩, ⟨decodeRow 12 ("67A01283459", 11), 219⟩, ⟨decodeRow 12 ("7A012834569", 11), 220⟩, ⟨decodeRow 12 ("A0128345679", 11), 221⟩, ⟨decodeRow 12 ("012834567A9", 11), 222⟩, ⟨decodeRow 12 ("12834567A09", 9), 223⟩, ⟨decodeRow 12 ("9128345670A", 9), 222⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A9128345607", 11), 221⟩, ⟨decodeRow 12 ("912834560A7", 11), 222⟩, ⟨decodeRow 12 ("12834560A97", 11), 223⟩, ⟨decodeRow 12 ("2834560A917", 11), 224⟩, ⟨decodeRow 12 ("834560A9127", 11), 225⟩, ⟨decodeRow 12 ("34560A91287", 11), 226⟩, ⟨decodeRow 12 ("4560A912837", 9), 227⟩, ⟨decodeRow 12 ("74560A91238", 11), 226⟩])
                (.leaf [⟨decodeRow 12 ("4560A912378", 11), 227⟩, ⟨decodeRow 12 ("560A9123748", 9), 228⟩, ⟨decodeRow 12 ("8560A912347", 11), 227⟩, ⟨decodeRow 12 ("560A9123487", 11), 228⟩, ⟨decodeRow 12 ("60A91234857", 9), 229⟩, ⟨decodeRow 12 ("760A9123458", 11), 228⟩, ⟨decodeRow 12 ("60A91234578", 11), 229⟩, ⟨decodeRow 12 ("0A912345768", 11), 230⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A9123457608", 11), 231⟩, ⟨decodeRow 12 ("912345760A8", 11), 232⟩, ⟨decodeRow 12 ("12345760A98", 11), 233⟩, ⟨decodeRow 12 ("2345760A918", 9), 234⟩, ⟨decodeRow 12 ("82345760A19", 11), 233⟩, ⟨decodeRow 12 ("2345760A189", 11), 234⟩, ⟨decodeRow 12 ("345760A1829", 11), 235⟩, ⟨decodeRow 12 ("45760A18239", 11), 236⟩])
                (.leaf [⟨decodeRow 12 ("5760A182349", 11), 237⟩, ⟨decodeRow 12 ("760A1823459", 11), 238⟩, ⟨decodeRow 12 ("60A18234579", 11), 239⟩, ⟨decodeRow 12 ("0A182345769", 9), 240⟩, ⟨decodeRow 12 ("90A18234567", 11), 239⟩, ⟨decodeRow 12 ("0A182345697", 11), 240⟩, ⟨decodeRow 12 ("A1823456907", 11), 241⟩, ⟨decodeRow 12 ("182345690A7", 11), 242⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("82345690A17", 11), 243⟩, ⟨decodeRow 12 ("2345690A187", 11), 244⟩, ⟨decodeRow 12 ("345690A1827", 9), 245⟩, ⟨decodeRow 12 ("7345690A128", 11), 244⟩, ⟨decodeRow 12 ("345690A1278", 11), 245⟩, ⟨decodeRow 12 ("45690A12738", 9), 246⟩, ⟨decodeRow 12 ("845690A1237", 11), 245⟩, ⟨decodeRow 12 ("45690A12387", 11), 246⟩])
                (.leaf [⟨decodeRow 12 ("5690A123847", 9), 247⟩, ⟨decodeRow 12 ("75690A12348", 11), 246⟩, ⟨decodeRow 12 ("5690A123478", 11), 247⟩, ⟨decodeRow 12 ("690A1234758", 11), 248⟩, ⟨decodeRow 12 ("90A12347568", 11), 249⟩, ⟨decodeRow 12 ("0A123475698", 11), 250⟩, ⟨decodeRow 12 ("A1234756908", 9), 251⟩, ⟨decodeRow 12 ("8A123475609", 11), 250⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A1234756089", 11), 251⟩, ⟨decodeRow 12 ("123475608A9", 11), 252⟩, ⟨decodeRow 12 ("23475608A19", 11), 253⟩, ⟨decodeRow 12 ("3475608A129", 11), 254⟩, ⟨decodeRow 12 ("475608A1239", 11), 255⟩, ⟨decodeRow 12 ("75608A12349", 11), 256⟩, ⟨decodeRow 12 ("5608A123479", 11), 257⟩, ⟨decodeRow 12 ("608A1234759", 9), 258⟩])
                (.leaf [⟨decodeRow 12 ("9608A123457", 11), 257⟩, ⟨decodeRow 12 ("608A1234597", 11), 258⟩, ⟨decodeRow 12 ("08A12345967", 11), 259⟩, ⟨decodeRow 12 ("8A123459607", 11), 260⟩, ⟨decodeRow 12 ("A1234596087", 11), 261⟩, ⟨decodeRow 12 ("123459608A7", 11), 262⟩, ⟨decodeRow 12 ("23459608A17", 9), 263⟩, ⟨decodeRow 12 ("7234596081A", 9), 262⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A7234596018", 11), 261⟩, ⟨decodeRow 12 ("723459601A8", 11), 262⟩, ⟨decodeRow 12 ("23459601A78", 11), 263⟩, ⟨decodeRow 12 ("3459601A728", 9), 264⟩, ⟨decodeRow 12 ("83459601A27", 11), 263⟩, ⟨decodeRow 12 ("3459601A287", 9), 264⟩, ⟨decodeRow 12 ("73459601A82", 9), 263⟩, ⟨decodeRow 12 ("2734596018A", 11), 262⟩])
                (.leaf [⟨decodeRow 12 ("7345960182A", 11), 263⟩, ⟨decodeRow 12 ("3459601827A", 11), 264⟩, ⟨decodeRow 12 ("4596018273A", 9), 265⟩, ⟨decodeRow 12 ("A4596018237", 11), 264⟩, ⟨decodeRow 12 ("459601823A7", 9), 265⟩, ⟨decodeRow 12 ("745960182A3", 9), 264⟩, ⟨decodeRow 12 ("374596018A2", 9), 263⟩, ⟨decodeRow 12 ("237459601A8", 11), 262⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("37459601A28", 11), 263⟩, ⟨decodeRow 12 ("7459601A238", 11), 264⟩, ⟨decodeRow 12 ("459601A2378", 11), 265⟩, ⟨decodeRow 12 ("59601A23748", 11), 266⟩, ⟨decodeRow 12 ("9601A237458", 11), 267⟩, ⟨decodeRow 12 ("601A2374598", 11), 268⟩, ⟨decodeRow 12 ("01A23745968", 9), 269⟩, ⟨decodeRow 12 ("801A2374569", 11), 268⟩])
                (.leaf [⟨decodeRow 12 ("01A23745689", 11), 269⟩, ⟨decodeRow 12 ("1A237456809", 11), 270⟩, ⟨decodeRow 12 ("A2374568019", 11), 271⟩, ⟨decodeRow 12 ("237456801A9", 11), 272⟩, ⟨decodeRow 12 ("37456801A29", 11), 273⟩, ⟨decodeRow 12 ("7456801A239", 11), 274⟩, ⟨decodeRow 12 ("456801A2379", 11), 275⟩, ⟨decodeRow 12 ("56801A23749", 9), 276⟩])))))))
    (.branch 254
      (.branch 127
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("956801A2347", 11), 275⟩, ⟨decodeRow 12 ("56801A23497", 11), 276⟩, ⟨decodeRow 12 ("6801A234957", 11), 277⟩, ⟨decodeRow 12 ("801A2349567", 11), 278⟩, ⟨decodeRow 12 ("01A23495687", 11), 279⟩, ⟨decodeRow 12 ("1A234956807", 9), 280⟩, ⟨decodeRow 12 ("71A23495608", 11), 279⟩])
                (.leaf [⟨decodeRow 12 ("1A234956078", 11), 280⟩, ⟨decodeRow 12 ("A2349560718", 9), 281⟩, ⟨decodeRow 12 ("8A234956017", 11), 280⟩, ⟨decodeRow 12 ("A2349560187", 11), 281⟩, ⟨decodeRow 12 ("234956018A7", 11), 282⟩, ⟨decodeRow 12 ("34956018A27", 9), 283⟩, ⟨decodeRow 12 ("7349560182A", 9), 282⟩, ⟨decodeRow 12 ("A7349560128", 11), 281⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("734956012A8", 11), 282⟩, ⟨decodeRow 12 ("34956012A78", 11), 283⟩, ⟨decodeRow 12 ("4956012A738", 11), 284⟩, ⟨decodeRow 12 ("956012A7348", 11), 285⟩, ⟨decodeRow 12 ("56012A73498", 11), 286⟩, ⟨decodeRow 12 ("6012A734958", 9), 287⟩, ⟨decodeRow 12 ("86012A73459", 11), 286⟩, ⟨decodeRow 12 ("6012A734589", 11), 287⟩])
                (.leaf [⟨decodeRow 12 ("012A7345869", 11), 288⟩, ⟨decodeRow 12 ("12A73458609", 11), 289⟩, ⟨decodeRow 12 ("2A734586019", 11), 290⟩, ⟨decodeRow 12 ("A7345860129", 11), 291⟩, ⟨decodeRow 12 ("734586012A9", 11), 292⟩, ⟨decodeRow 12 ("34586012A79", 11), 293⟩, ⟨decodeRow 12 ("4586012A739", 9), 294⟩, ⟨decodeRow 12 ("94586012A37", 11), 293⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("4586012A397", 11), 294⟩, ⟨decodeRow 12 ("586012A3947", 11), 295⟩, ⟨decodeRow 12 ("86012A39457", 11), 296⟩, ⟨decodeRow 12 ("6012A394587", 11), 297⟩, ⟨decodeRow 12 ("012A3945867", 9), 298⟩, ⟨decodeRow 12 ("7012A394568", 11), 297⟩, ⟨decodeRow 12 ("012A3945678", 11), 298⟩, ⟨decodeRow 12 ("12A39456708", 9), 299⟩])
                (.leaf [⟨decodeRow 12 ("812A3945607", 11), 298⟩, ⟨decodeRow 12 ("12A39456087", 11), 299⟩, ⟨decodeRow 12 ("2A394560817", 9), 300⟩, ⟨decodeRow 12 ("72A39456018", 11), 299⟩, ⟨decodeRow 12 ("2A394560178", 11), 300⟩, ⟨decodeRow 12 ("A3945601728", 11), 301⟩, ⟨decodeRow 12 ("394560172A8", 11), 302⟩, ⟨decodeRow 12 ("94560172A38", 11), 303⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("4560172A398", 11), 304⟩, ⟨decodeRow 12 ("560172A3948", 9), 305⟩, ⟨decodeRow 12 ("8560172A349", 11), 304⟩, ⟨decodeRow 12 ("560172A3489", 11), 305⟩, ⟨decodeRow 12 ("60172A34859", 11), 306⟩, ⟨decodeRow 12 ("0172A348569", 11), 307⟩, ⟨decodeRow 12 ("172A3485609", 11), 308⟩, ⟨decodeRow 12 ("72A34856019", 11), 309⟩])
                (.leaf [⟨decodeRow 12 ("2A348560179", 11), 310⟩, ⟨decodeRow 12 ("A3485601729", 9), 311⟩, ⟨decodeRow 12 ("9A348560127", 11), 310⟩, ⟨decodeRow 12 ("A3485601297", 11), 311⟩, ⟨decodeRow 12 ("348560129A7", 11), 312⟩, ⟨decodeRow 12 ("48560129A37", 11), 313⟩, ⟨decodeRow 12 ("8560129A347", 11), 314⟩, ⟨decodeRow 12 ("560129A3487", 11), 315⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("60129A34857", 9), 316⟩, ⟨decodeRow 12 ("760129A3458", 11), 315⟩, ⟨decodeRow 12 ("60129A34578", 11), 316⟩, ⟨decodeRow 12 ("0129A345768", 9), 317⟩, ⟨decodeRow 12 ("80129A34567", 11), 316⟩, ⟨decodeRow 12 ("0129A345687", 11), 317⟩, ⟨decodeRow 12 ("129A3456807", 9), 318⟩, ⟨decodeRow 12 ("7129A345608", 11), 317⟩])
                (.leaf [⟨decodeRow 12 ("129A3456078", 11), 318⟩, ⟨decodeRow 12 ("29A34560718", 11), 319⟩, ⟨decodeRow 12 ("9A345607128", 11), 320⟩, ⟨decodeRow 12 ("A3456071298", 11), 321⟩, ⟨decodeRow 12 ("345607129A8", 11), 322⟩, ⟨decodeRow 12 ("45607129A38", 9), 323⟩, ⟨decodeRow 12 ("8456071293A", 9), 322⟩, ⟨decodeRow 12 ("A8456071239", 11), 321⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("845607123A9", 11), 322⟩, ⟨decodeRow 12 ("45607123A89", 11), 323⟩, ⟨decodeRow 12 ("5607123A849", 11), 324⟩, ⟨decodeRow 12 ("607123A8459", 11), 325⟩, ⟨decodeRow 12 ("07123A84569", 11), 326⟩, ⟨decodeRow 12 ("7123A845609", 11), 327⟩, ⟨decodeRow 12 ("123A8456079", 11), 328⟩, ⟨decodeRow 12 ("23A84560719", 9), 329⟩])
                (.leaf [⟨decodeRow 12 ("923A8456017", 11), 328⟩, ⟨decodeRow 12 ("23A84560197", 11), 329⟩, ⟨decodeRow 12 ("3A845601927", 11), 330⟩, ⟨decodeRow 12 ("A8456019237", 11), 331⟩, ⟨decodeRow 12 ("845601923A7", 11), 332⟩, ⟨decodeRow 12 ("45601923A87", 11), 333⟩, ⟨decodeRow 12 ("5601923A847", 9), 334⟩, ⟨decodeRow 12 ("75601923A48", 11), 333⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("5601923A478", 9), 334⟩, ⟨decodeRow 12 ("85601923A74", 9), 333⟩, ⟨decodeRow 12 ("4856019237A", 11), 332⟩, ⟨decodeRow 12 ("8560192374A", 11), 333⟩, ⟨decodeRow 12 ("5601923748A", 11), 334⟩, ⟨decodeRow 12 ("6019237485A", 9), 335⟩, ⟨decodeRow 12 ("A6019237458", 11), 334⟩, ⟨decodeRow 12 ("601923745A8", 9), 335⟩])
                (.leaf [⟨decodeRow 12 ("860192374A5", 9), 334⟩, ⟨decodeRow 12 ("586019237A4", 9), 333⟩, ⟨decodeRow 12 ("458601923A7", 11), 332⟩, ⟨decodeRow 12 ("58601923A47", 11), 333⟩, ⟨decodeRow 12 ("8601923A457", 11), 334⟩, ⟨decodeRow 12 ("601923A4587", 11), 335⟩, ⟨decodeRow 12 ("01923A45867", 9), 336⟩, ⟨decodeRow 12 ("701923A4568", 11), 335⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("01923A45678", 11), 336⟩, ⟨decodeRow 12 ("1923A456708", 11), 337⟩, ⟨decodeRow 12 ("923A4567018", 11), 338⟩, ⟨decodeRow 12 ("23A45670198", 11), 339⟩, ⟨decodeRow 12 ("3A456701928", 9), 340⟩, ⟨decodeRow 12 ("83A45670129", 11), 339⟩, ⟨decodeRow 12 ("3A456701289", 11), 340⟩, ⟨decodeRow 12 ("A4567012839", 11), 341⟩])
                (.leaf [⟨decodeRow 12 ("456701283A9", 11), 342⟩, ⟨decodeRow 12 ("56701283A49", 11), 343⟩, ⟨decodeRow 12 ("6701283A459", 11), 344⟩, ⟨decodeRow 12 ("701283A4569", 11), 345⟩, ⟨decodeRow 12 ("01283A45679", 11), 346⟩, ⟨decodeRow 12 ("1283A456709", 9), 347⟩, ⟨decodeRow 12 ("91283A45607", 11), 346⟩, ⟨decodeRow 12 ("1283A456097", 11), 347⟩])))))
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("283A4560917", 11), 348⟩, ⟨decodeRow 12 ("83A45609127", 11), 349⟩, ⟨decodeRow 12 ("3A456091287", 11), 350⟩, ⟨decodeRow 12 ("A4560912837", 9), 351⟩, ⟨decodeRow 12 ("7A456091238", 11), 350⟩, ⟨decodeRow 12 ("A4560912378", 11), 351⟩, ⟨decodeRow 12 ("456091237A8", 11), 352⟩])
                (.leaf [⟨decodeRow 12 ("56091237A48", 9), 353⟩, ⟨decodeRow 12 ("8560912374A", 9), 352⟩, ⟨decodeRow 12 ("A8560912347", 11), 351⟩, ⟨decodeRow 12 ("856091234A7", 11), 352⟩, ⟨decodeRow 12 ("56091234A87", 11), 353⟩, ⟨decodeRow 12 ("6091234A857", 9), 354⟩, ⟨decodeRow 12 ("76091234A58", 11), 353⟩, ⟨decodeRow 12 ("6091234A578", 11), 354⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("091234A5768", 11), 355⟩, ⟨decodeRow 12 ("91234A57608", 11), 356⟩, ⟨decodeRow 12 ("1234A576098", 11), 357⟩, ⟨decodeRow 12 ("234A5760918", 9), 358⟩, ⟨decodeRow 12 ("8234A576019", 11), 357⟩, ⟨decodeRow 12 ("234A5760189", 11), 358⟩, ⟨decodeRow 12 ("34A57601829", 11), 359⟩, ⟨decodeRow 12 ("4A576018239", 11), 360⟩])
                (.leaf [⟨decodeRow 12 ("A5760182349", 11), 361⟩, ⟨decodeRow 12 ("576018234A9", 11), 362⟩, ⟨decodeRow 12 ("76018234A59", 11), 363⟩, ⟨decodeRow 12 ("6018234A579", 11), 364⟩, ⟨decodeRow 12 ("018234A5769", 9), 365⟩, ⟨decodeRow 12 ("9018234A567", 11), 364⟩, ⟨decodeRow 12 ("018234A5697", 11), 365⟩, ⟨decodeRow 12 ("18234A56907", 11), 366⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("8234A569017", 11), 367⟩, ⟨decodeRow 12 ("234A5690187", 11), 368⟩, ⟨decodeRow 12 ("34A56901827", 9), 369⟩, ⟨decodeRow 12 ("734A5690128", 11), 368⟩, ⟨decodeRow 12 ("34A56901278", 11), 369⟩, ⟨decodeRow 12 ("4A569012738", 11), 370⟩, ⟨decodeRow 12 ("A5690127348", 11), 371⟩, ⟨decodeRow 12 ("569012734A8", 9), 372⟩])
                (.leaf [⟨decodeRow 12 ("856901273A4", 9), 371⟩, ⟨decodeRow 12 ("485690127A3", 9), 370⟩, ⟨decodeRow 12 ("348569012A7", 11), 369⟩, ⟨decodeRow 12 ("48569012A37", 9), 370⟩, ⟨decodeRow 12 ("7485690123A", 11), 369⟩, ⟨decodeRow 12 ("4856901237A", 11), 370⟩, ⟨decodeRow 12 ("8569012374A", 11), 371⟩, ⟨decodeRow 12 ("5690123748A", 9), 372⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A5690123784", 9), 371⟩, ⟨decodeRow 12 ("4A569012387", 11), 370⟩, ⟨decodeRow 12 ("A5690123847", 9), 371⟩, ⟨decodeRow 12 ("7A569012348", 11), 370⟩, ⟨decodeRow 12 ("A5690123478", 11), 371⟩, ⟨decodeRow 12 ("569012347A8", 11), 372⟩, ⟨decodeRow 12 ("69012347A58", 11), 373⟩, ⟨decodeRow 12 ("9012347A568", 11), 374⟩])
                (.leaf [⟨decodeRow 12 ("012347A5698", 11), 375⟩, ⟨decodeRow 12 ("12347A56908", 9), 376⟩, ⟨decodeRow 12 ("812347A5609", 11), 375⟩, ⟨decodeRow 12 ("12347A56089", 11), 376⟩, ⟨decodeRow 12 ("2347A560819", 11), 377⟩, ⟨decodeRow 12 ("347A5608129", 11), 378⟩, ⟨decodeRow 12 ("47A56081239", 11), 379⟩, ⟨decodeRow 12 ("7A560812349", 11), 380⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A5608123479", 11), 381⟩, ⟨decodeRow 12 ("560812347A9", 11), 382⟩, ⟨decodeRow 12 ("60812347A59", 9), 383⟩, ⟨decodeRow 12 ("9608123475A", 9), 382⟩, ⟨decodeRow 12 ("A9608123457", 11), 381⟩, ⟨decodeRow 12 ("960812345A7", 11), 382⟩, ⟨decodeRow 12 ("60812345A97", 11), 383⟩, ⟨decodeRow 12 ("0812345A967", 11), 384⟩])
                (.leaf [⟨decodeRow 12 ("812345A9607", 11), 385⟩, ⟨decodeRow 12 ("12345A96087", 11), 386⟩, ⟨decodeRow 12 ("2345A960817", 9), 387⟩, ⟨decodeRow 12 ("72345A96018", 11), 386⟩, ⟨decodeRow 12 ("2345A960178", 11), 387⟩, ⟨decodeRow 12 ("345A9601728", 9), 388⟩, ⟨decodeRow 12 ("8345A960127", 11), 387⟩, ⟨decodeRow 12 ("345A9601287", 11), 388⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("45A96012837", 9), 389⟩, ⟨decodeRow 12 ("745A9601238", 11), 388⟩, ⟨decodeRow 12 ("45A96012378", 11), 389⟩, ⟨decodeRow 12 ("5A960123748", 11), 390⟩, ⟨decodeRow 12 ("A9601237458", 11), 391⟩, ⟨decodeRow 12 ("960123745A8", 11), 392⟩, ⟨decodeRow 12 ("60123745A98", 11), 393⟩, ⟨decodeRow 12 ("0123745A968", 9), 394⟩])
                (.leaf [⟨decodeRow 12 ("80123745A69", 11), 393⟩, ⟨decodeRow 12 ("0123745A689", 11), 394⟩, ⟨decodeRow 12 ("123745A6809", 11), 395⟩, ⟨decodeRow 12 ("23745A68019", 11), 396⟩, ⟨decodeRow 12 ("3745A680129", 11), 397⟩, ⟨decodeRow 12 ("745A6801239", 11), 398⟩, ⟨decodeRow 12 ("45A68012379", 11), 399⟩, ⟨decodeRow 12 ("5A680123749", 9), 400⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("95A68012347", 11), 399⟩, ⟨decodeRow 12 ("5A680123497", 11), 400⟩, ⟨decodeRow 12 ("A6801234957", 11), 401⟩, ⟨decodeRow 12 ("680123495A7", 11), 402⟩, ⟨decodeRow 12 ("80123495A67", 11), 403⟩, ⟨decodeRow 12 ("0123495A687", 11), 404⟩, ⟨decodeRow 12 ("123495A6807", 9), 405⟩, ⟨decodeRow 12 ("7123495A608", 11), 404⟩])
                (.leaf [⟨decodeRow 12 ("123495A6078", 11), 405⟩, ⟨decodeRow 12 ("23495A60718", 9), 406⟩, ⟨decodeRow 12 ("823495A6017", 11), 405⟩, ⟨decodeRow 12 ("23495A60187", 11), 406⟩, ⟨decodeRow 12 ("3495A601827", 9), 407⟩, ⟨decodeRow 12 ("73495A60128", 11), 406⟩, ⟨decodeRow 12 ("3495A601278", 11), 407⟩, ⟨decodeRow 12 ("495A6012738", 11), 408⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("95A60127348", 11), 409⟩, ⟨decodeRow 12 ("5A601273498", 11), 410⟩, ⟨decodeRow 12 ("A6012734958", 9), 411⟩, ⟨decodeRow 12 ("8A601273459", 11), 410⟩, ⟨decodeRow 12 ("A6012734589", 11), 411⟩, ⟨decodeRow 12 ("601273458A9", 11), 412⟩, ⟨decodeRow 12 ("01273458A69", 11), 413⟩, ⟨decodeRow 12 ("1273458A609", 11), 414⟩])
                (.leaf [⟨decodeRow 12 ("273458A6019", 11), 415⟩, ⟨decodeRow 12 ("73458A60129", 11), 416⟩, ⟨decodeRow 12 ("3458A601279", 11), 417⟩, ⟨decodeRow 12 ("458A6012739", 9), 418⟩, ⟨decodeRow 12 ("9458A601237", 11), 417⟩, ⟨decodeRow 12 ("458A6012397", 11), 418⟩, ⟨decodeRow 12 ("58A60123947", 11), 419⟩, ⟨decodeRow 12 ("8A601239457", 11), 420⟩]))))))
      (.branch 127
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("A6012394587", 11), 421⟩, ⟨decodeRow 12 ("601239458A7", 11), 422⟩, ⟨decodeRow 12 ("01239458A67", 9), 423⟩, ⟨decodeRow 12 ("7012394586A", 9), 422⟩, ⟨decodeRow 12 ("A7012394568", 11), 421⟩, ⟨decodeRow 12 ("701239456A8", 11), 422⟩, ⟨decodeRow 12 ("01239456A78", 11), 423⟩])
                (.leaf [⟨decodeRow 12 ("1239456A708", 9), 424⟩, ⟨decodeRow 12 ("81239456A07", 11), 423⟩, ⟨decodeRow 12 ("1239456A087", 9), 424⟩, ⟨decodeRow 12 ("71239456A80", 9), 423⟩, ⟨decodeRow 12 ("0712394568A", 11), 422⟩, ⟨decodeRow 12 ("7123945680A", 11), 423⟩, ⟨decodeRow 12 ("1239456807A", 11), 424⟩, ⟨decodeRow 12 ("2394568071A", 9), 425⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A2394568017", 11), 424⟩, ⟨decodeRow 12 ("239456801A7", 9), 425⟩, ⟨decodeRow 12 ("723945680A1", 9), 424⟩, ⟨decodeRow 12 ("172394568A0", 9), 423⟩, ⟨decodeRow 12 ("017239456A8", 11), 422⟩, ⟨decodeRow 12 ("17239456A08", 11), 423⟩, ⟨decodeRow 12 ("7239456A018", 11), 424⟩, ⟨decodeRow 12 ("239456A0178", 11), 425⟩])
                (.leaf [⟨decodeRow 12 ("39456A01728", 11), 426⟩, ⟨decodeRow 12 ("9456A017238", 11), 427⟩, ⟨decodeRow 12 ("456A0172398", 11), 428⟩, ⟨decodeRow 12 ("56A01723948", 9), 429⟩, ⟨decodeRow 12 ("856A0172349", 11), 428⟩, ⟨decodeRow 12 ("56A01723489", 11), 429⟩, ⟨decodeRow 12 ("6A017234859", 11), 430⟩, ⟨decodeRow 12 ("A0172348569", 11), 431⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("017234856A9", 11), 432⟩, ⟨decodeRow 12 ("17234856A09", 11), 433⟩, ⟨decodeRow 12 ("7234856A019", 11), 434⟩, ⟨decodeRow 12 ("234856A0179", 11), 435⟩, ⟨decodeRow 12 ("34856A01729", 9), 436⟩, ⟨decodeRow 12 ("934856A0127", 11), 435⟩, ⟨decodeRow 12 ("34856A01297", 11), 436⟩, ⟨decodeRow 12 ("4856A012937", 11), 437⟩])
                (.leaf [⟨decodeRow 12 ("856A0129347", 11), 438⟩, ⟨decodeRow 12 ("56A01293487", 11), 439⟩, ⟨decodeRow 12 ("6A012934857", 9), 440⟩, ⟨decodeRow 12 ("76A01293458", 11), 439⟩, ⟨decodeRow 12 ("6A012934578", 11), 440⟩, ⟨decodeRow 12 ("A0129345768", 9), 441⟩, ⟨decodeRow 12 ("8A012934567", 11), 440⟩, ⟨decodeRow 12 ("A0129345687", 11), 441⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("012934568A7", 11), 442⟩, ⟨decodeRow 12 ("12934568A07", 9), 443⟩, ⟨decodeRow 12 ("7129345680A", 9), 442⟩, ⟨decodeRow 12 ("A7129345608", 11), 441⟩, ⟨decodeRow 12 ("712934560A8", 11), 442⟩, ⟨decodeRow 12 ("12934560A78", 11), 443⟩, ⟨decodeRow 12 ("2934560A718", 11), 444⟩, ⟨decodeRow 12 ("934560A7128", 11), 445⟩])
                (.leaf [⟨decodeRow 12 ("34560A71298", 11), 446⟩, ⟨decodeRow 12 ("4560A712938", 9), 447⟩, ⟨decodeRow 12 ("84560A71239", 11), 446⟩, ⟨decodeRow 12 ("4560A712389", 11), 447⟩, ⟨decodeRow 12 ("560A7123849", 11), 448⟩, ⟨decodeRow 12 ("60A71238459", 11), 449⟩, ⟨decodeRow 12 ("0A712384569", 11), 450⟩, ⟨decodeRow 12 ("A7123845609", 11), 451⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("712384560A9", 11), 452⟩, ⟨decodeRow 12 ("12384560A79", 11), 453⟩, ⟨decodeRow 12 ("2384560A719", 9), 454⟩, ⟨decodeRow 12 ("92384560A17", 11), 453⟩, ⟨decodeRow 12 ("2384560A197", 11), 454⟩, ⟨decodeRow 12 ("384560A1927", 11), 455⟩, ⟨decodeRow 12 ("84560A19237", 11), 456⟩, ⟨decodeRow 12 ("4560A192387", 11), 457⟩])
                (.leaf [⟨decodeRow 12 ("560A1923847", 9), 458⟩, ⟨decodeRow 12 ("7560A192348", 11), 457⟩, ⟨decodeRow 12 ("560A1923478", 11), 458⟩, ⟨decodeRow 12 ("60A19234758", 9), 459⟩, ⟨decodeRow 12 ("860A1923457", 11), 458⟩, ⟨decodeRow 12 ("60A19234587", 11), 459⟩, ⟨decodeRow 12 ("0A192345867", 9), 460⟩, ⟨decodeRow 12 ("70A19234568", 11), 459⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("0A192345678", 11), 460⟩, ⟨decodeRow 12 ("A1923456708", 11), 461⟩, ⟨decodeRow 12 ("192345670A8", 11), 462⟩, ⟨decodeRow 12 ("92345670A18", 11), 463⟩, ⟨decodeRow 12 ("2345670A198", 11), 464⟩, ⟨decodeRow 12 ("345670A1928", 9), 465⟩, ⟨decodeRow 12 ("8345670A129", 11), 464⟩, ⟨decodeRow 12 ("345670A1289", 11), 465⟩])
                (.leaf [⟨decodeRow 12 ("45670A12839", 11), 466⟩, ⟨decodeRow 12 ("5670A128349", 11), 467⟩, ⟨decodeRow 12 ("670A1283459", 11), 468⟩, ⟨decodeRow 12 ("70A12834569", 11), 469⟩, ⟨decodeRow 12 ("0A128345679", 11), 470⟩, ⟨decodeRow 12 ("A1283456709", 9), 471⟩, ⟨decodeRow 12 ("9A128345607", 11), 470⟩, ⟨decodeRow 12 ("A1283456097", 11), 471⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("128345609A7", 11), 472⟩, ⟨decodeRow 12 ("28345609A17", 11), 473⟩, ⟨decodeRow 12 ("8345609A127", 11), 474⟩, ⟨decodeRow 12 ("345609A1287", 11), 475⟩, ⟨decodeRow 12 ("45609A12837", 9), 476⟩, ⟨decodeRow 12 ("745609A1238", 11), 475⟩, ⟨decodeRow 12 ("45609A12378", 11), 476⟩, ⟨decodeRow 12 ("5609A123748", 9), 477⟩])
                (.leaf [⟨decodeRow 12 ("85609A12347", 11), 476⟩, ⟨decodeRow 12 ("5609A123487", 11), 477⟩, ⟨decodeRow 12 ("609A1234857", 9), 478⟩, ⟨decodeRow 12 ("7609A123458", 11), 477⟩, ⟨decodeRow 12 ("609A1234578", 11), 478⟩, ⟨decodeRow 12 ("09A12345768", 11), 479⟩, ⟨decodeRow 12 ("9A123457608", 11), 480⟩, ⟨decodeRow 12 ("A1234576098", 11), 481⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("123457609A8", 11), 482⟩, ⟨decodeRow 12 ("23457609A18", 9), 483⟩, ⟨decodeRow 12 ("8234576091A", 9), 482⟩, ⟨decodeRow 12 ("A8234576019", 11), 481⟩, ⟨decodeRow 12 ("823457601A9", 11), 482⟩, ⟨decodeRow 12 ("23457601A89", 11), 483⟩, ⟨decodeRow 12 ("3457601A829", 11), 484⟩, ⟨decodeRow 12 ("457601A8239", 11), 485⟩])
                (.leaf [⟨decodeRow 12 ("57601A82349", 11), 486⟩, ⟨decodeRow 12 ("7601A823459", 11), 487⟩, ⟨decodeRow 12 ("601A8234579", 11), 488⟩, ⟨decodeRow 12 ("01A82345769", 9), 489⟩, ⟨decodeRow 12 ("901A8234567", 11), 488⟩, ⟨decodeRow 12 ("01A82345697", 11), 489⟩, ⟨decodeRow 12 ("1A823456907", 11), 490⟩, ⟨decodeRow 12 ("A8234569017", 11), 491⟩])))))
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("823456901A7", 11), 492⟩, ⟨decodeRow 12 ("23456901A87", 11), 493⟩, ⟨decodeRow 12 ("3456901A827", 9), 494⟩, ⟨decodeRow 12 ("73456901A28", 11), 493⟩, ⟨decodeRow 12 ("3456901A278", 9), 494⟩, ⟨decodeRow 12 ("83456901A72", 9), 493⟩, ⟨decodeRow 12 ("2834569017A", 11), 492⟩])
                (.leaf [⟨decodeRow 12 ("8345690172A", 11), 493⟩, ⟨decodeRow 12 ("3456901728A", 11), 494⟩, ⟨decodeRow 12 ("4569017283A", 9), 495⟩, ⟨decodeRow 12 ("A4569017238", 11), 494⟩, ⟨decodeRow 12 ("456901723A8", 9), 495⟩, ⟨decodeRow 12 ("845690172A3", 9), 494⟩, ⟨decodeRow 12 ("384569017A2", 9), 493⟩, ⟨decodeRow 12 ("238456901A7", 11), 492⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("38456901A27", 11), 493⟩, ⟨decodeRow 12 ("8456901A237", 11), 494⟩, ⟨decodeRow 12 ("456901A2387", 11), 495⟩, ⟨decodeRow 12 ("56901A23847", 9), 496⟩, ⟨decodeRow 12 ("756901A2348", 11), 495⟩, ⟨decodeRow 12 ("56901A23478", 11), 496⟩, ⟨decodeRow 12 ("6901A234758", 11), 497⟩, ⟨decodeRow 12 ("901A2347568", 11), 498⟩])
                (.leaf [⟨decodeRow 12 ("01A23475698", 11), 499⟩, ⟨decodeRow 12 ("1A234756908", 9), 500⟩, ⟨decodeRow 12 ("81A23475609", 11), 499⟩, ⟨decodeRow 12 ("1A234756089", 11), 500⟩, ⟨decodeRow 12 ("A2347560819", 11), 501⟩, ⟨decodeRow 12 ("234756081A9", 11), 502⟩, ⟨decodeRow 12 ("34756081A29", 11), 503⟩, ⟨decodeRow 12 ("4756081A239", 11), 504⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("756081A2349", 11), 505⟩, ⟨decodeRow 12 ("56081A23479", 11), 506⟩, ⟨decodeRow 12 ("6081A234759", 9), 507⟩, ⟨decodeRow 12 ("96081A23457", 11), 506⟩, ⟨decodeRow 12 ("6081A234597", 11), 507⟩, ⟨decodeRow 12 ("081A2345967", 11), 508⟩, ⟨decodeRow 12 ("81A23459607", 11), 509⟩, ⟨decodeRow 12 ("1A234596087", 11), 510⟩])
                (.leaf [⟨decodeRow 12 ("A2345960817", 9), 511⟩, ⟨decodeRow 12 ("7A234596018", 11), 510⟩, ⟨decodeRow 12 ("A2345960178", 11), 511⟩, ⟨decodeRow 12 ("234596017A8", 11), 512⟩, ⟨decodeRow 12 ("34596017A28", 9), 513⟩, ⟨decodeRow 12 ("8345960172A", 9), 512⟩, ⟨decodeRow 12 ("A8345960127", 11), 511⟩, ⟨decodeRow 12 ("834596012A7", 11), 512⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("34596012A87", 11), 513⟩, ⟨decodeRow 12 ("4596012A837", 9), 514⟩, ⟨decodeRow 12 ("74596012A38", 11), 513⟩, ⟨decodeRow 12 ("4596012A378", 11), 514⟩, ⟨decodeRow 12 ("596012A3748", 11), 515⟩, ⟨decodeRow 12 ("96012A37458", 11), 516⟩, ⟨decodeRow 12 ("6012A374598", 11), 517⟩, ⟨decodeRow 12 ("012A3745968", 9), 518⟩])
                (.leaf [⟨decodeRow 12 ("8012A374569", 11), 517⟩, ⟨decodeRow 12 ("012A3745689", 11), 518⟩, ⟨decodeRow 12 ("12A37456809", 11), 519⟩, ⟨decodeRow 12 ("2A374568019", 11), 520⟩, ⟨decodeRow 12 ("A3745680129", 11), 521⟩, ⟨decodeRow 12 ("374568012A9", 11), 522⟩, ⟨decodeRow 12 ("74568012A39", 11), 523⟩, ⟨decodeRow 12 ("4568012A379", 11), 524⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("568012A3749", 9), 525⟩, ⟨decodeRow 12 ("9568012A347", 11), 524⟩, ⟨decodeRow 12 ("568012A3497", 11), 525⟩, ⟨decodeRow 12 ("68012A34957", 11), 526⟩, ⟨decodeRow 12 ("8012A349567", 11), 527⟩, ⟨decodeRow 12 ("012A3495687", 11), 528⟩, ⟨decodeRow 12 ("12A34956807", 9), 529⟩, ⟨decodeRow 12 ("712A3495608", 11), 528⟩])
                (.leaf [⟨decodeRow 12 ("12A34956078", 11), 529⟩, ⟨decodeRow 12 ("2A349560718", 11), 530⟩, ⟨decodeRow 12 ("A3495607128", 11), 531⟩, ⟨decodeRow 12 ("349560712A8", 9), 532⟩, ⟨decodeRow 12 ("834956071A2", 9), 531⟩, ⟨decodeRow 12 ("283495607A1", 9), 530⟩, ⟨decodeRow 12 ("128349560A7", 11), 529⟩, ⟨decodeRow 12 ("28349560A17", 9), 530⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("7283495601A", 11), 529⟩, ⟨decodeRow 12 ("2834956017A", 11), 530⟩, ⟨decodeRow 12 ("8349560172A", 11), 531⟩, ⟨decodeRow 12 ("3495601728A", 9), 532⟩, ⟨decodeRow 12 ("A3495601782", 9), 531⟩, ⟨decodeRow 12 ("2A349560187", 11), 530⟩, ⟨decodeRow 12 ("A3495601827", 9), 531⟩, ⟨decodeRow 12 ("7A349560128", 11), 530⟩])
                (.leaf [⟨decodeRow 12 ("A3495601278", 11), 531⟩, ⟨decodeRow 12 ("349560127A8", 11), 532⟩, ⟨decodeRow 12 ("49560127A38", 11), 533⟩, ⟨decodeRow 12 ("9560127A348", 11), 534⟩, ⟨decodeRow 12 ("560127A3498", 11), 535⟩, ⟨decodeRow 12 ("60127A34958", 9), 536⟩, ⟨decodeRow 12 ("860127A3459", 11), 535⟩, ⟨decodeRow 12 ("60127A34589", 11), 536⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("0127A345869", 11), 537⟩, ⟨decodeRow 12 ("127A3458609", 11), 538⟩, ⟨decodeRow 12 ("27A34586019", 11), 539⟩, ⟨decodeRow 12 ("7A345860129", 11), 540⟩, ⟨decodeRow 12 ("A3458601279", 11), 541⟩, ⟨decodeRow 12 ("345860127A9", 11), 542⟩, ⟨decodeRow 12 ("45860127A39", 9), 543⟩, ⟨decodeRow 12 ("9458601273A", 9), 542⟩])
                (.leaf [⟨decodeRow 12 ("A9458601237", 11), 541⟩, ⟨decodeRow 12 ("945860123A7", 11), 542⟩, ⟨decodeRow 12 ("45860123A97", 11), 543⟩, ⟨decodeRow 12 ("5860123A947", 11), 544⟩, ⟨decodeRow 12 ("860123A9457", 11), 545⟩, ⟨decodeRow 12 ("60123A94587", 11), 546⟩, ⟨decodeRow 12 ("0123A945867", 9), 547⟩, ⟨decodeRow 12 ("70123A94568", 11), 546⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("0123A945678", 11), 547⟩, ⟨decodeRow 12 ("123A9456708", 9), 548⟩, ⟨decodeRow 12 ("8123A945607", 11), 547⟩, ⟨decodeRow 12 ("123A9456087", 11), 548⟩, ⟨decodeRow 12 ("23A94560817", 9), 549⟩, ⟨decodeRow 12 ("723A9456018", 11), 548⟩, ⟨decodeRow 12 ("23A94560178", 11), 549⟩, ⟨decodeRow 12 ("3A945601728", 11), 550⟩])
                (.leaf [⟨decodeRow 12 ("A9456017238", 11), 551⟩, ⟨decodeRow 12 ("945601723A8", 11), 552⟩, ⟨decodeRow 12 ("45601723A98", 11), 553⟩, ⟨decodeRow 12 ("5601723A948", 9), 554⟩, ⟨decodeRow 12 ("85601723A49", 11), 553⟩, ⟨decodeRow 12 ("5601723A489", 11), 554⟩, ⟨decodeRow 12 ("601723A4859", 11), 555⟩, ⟨decodeRow 12 ("01723A48569", 11), 556⟩]))))))))
  (.branch 507
    (.branch 253
      (.branch 126
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("1723A485609", 11), 557⟩, ⟨decodeRow 12 ("723A4856019", 11), 558⟩, ⟨decodeRow 12 ("23A48560179", 11), 559⟩, ⟨decodeRow 12 ("3A485601729", 9), 560⟩, ⟨decodeRow 12 ("93A48560127", 11), 559⟩, ⟨decodeRow 12 ("3A485601297", 11), 560⟩, ⟨decodeRow 12 ("A4856012937", 11), 561⟩])
                (.leaf [⟨decodeRow 12 ("485601293A7", 11), 562⟩, ⟨decodeRow 12 ("85601293A47", 11), 563⟩, ⟨decodeRow 12 ("5601293A487", 11), 564⟩, ⟨decodeRow 12 ("601293A4857", 9), 565⟩, ⟨decodeRow 12 ("7601293A458", 11), 564⟩, ⟨decodeRow 12 ("601293A4578", 11), 565⟩, ⟨decodeRow 12 ("01293A45768", 9), 566⟩, ⟨decodeRow 12 ("801293A4567", 11), 565⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("01293A45687", 11), 566⟩, ⟨decodeRow 12 ("1293A456807", 9), 567⟩, ⟨decodeRow 12 ("71293A45608", 11), 566⟩, ⟨decodeRow 12 ("1293A456078", 11), 567⟩, ⟨decodeRow 12 ("293A4560718", 11), 568⟩, ⟨decodeRow 12 ("93A45607128", 11), 569⟩, ⟨decodeRow 12 ("3A456071298", 11), 570⟩, ⟨decodeRow 12 ("A4560712938", 9), 571⟩])
                (.leaf [⟨decodeRow 12 ("8A456071239", 11), 570⟩, ⟨decodeRow 12 ("A4560712389", 11), 571⟩, ⟨decodeRow 12 ("456071238A9", 11), 572⟩, ⟨decodeRow 12 ("56071238A49", 11), 573⟩, ⟨decodeRow 12 ("6071238A459", 11), 574⟩, ⟨decodeRow 12 ("071238A4569", 11), 575⟩, ⟨decodeRow 12 ("71238A45609", 11), 576⟩, ⟨decodeRow 12 ("1238A456079", 11), 577⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("238A4560719", 9), 578⟩, ⟨decodeRow 12 ("9238A456017", 11), 577⟩, ⟨decodeRow 12 ("238A4560197", 11), 578⟩, ⟨decodeRow 12 ("38A45601927", 11), 579⟩, ⟨decodeRow 12 ("8A456019237", 11), 580⟩, ⟨decodeRow 12 ("A4560192387", 11), 581⟩, ⟨decodeRow 12 ("456019238A7", 11), 582⟩, ⟨decodeRow 12 ("56019238A47", 9), 583⟩])
                (.leaf [⟨decodeRow 12 ("7560192384A", 9), 582⟩, ⟨decodeRow 12 ("A7560192348", 11), 581⟩, ⟨decodeRow 12 ("756019234A8", 11), 582⟩, ⟨decodeRow 12 ("56019234A78", 11), 583⟩, ⟨decodeRow 12 ("6019234A758", 9), 584⟩, ⟨decodeRow 12 ("86019234A57", 11), 583⟩, ⟨decodeRow 12 ("6019234A587", 9), 584⟩, ⟨decodeRow 12 ("76019234A85", 9), 583⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("5760192348A", 11), 582⟩, ⟨decodeRow 12 ("7601923485A", 11), 583⟩, ⟨decodeRow 12 ("6019234857A", 11), 584⟩, ⟨decodeRow 12 ("0192348576A", 9), 585⟩, ⟨decodeRow 12 ("A0192348567", 11), 584⟩, ⟨decodeRow 12 ("019234856A7", 9), 585⟩, ⟨decodeRow 12 ("701923485A6", 9), 584⟩, ⟨decodeRow 12 ("670192348A5", 9), 583⟩])
                (.leaf [⟨decodeRow 12 ("567019234A8", 11), 582⟩, ⟨decodeRow 12 ("67019234A58", 11), 583⟩, ⟨decodeRow 12 ("7019234A568", 11), 584⟩, ⟨decodeRow 12 ("019234A5678", 11), 585⟩, ⟨decodeRow 12 ("19234A56708", 11), 586⟩, ⟨decodeRow 12 ("9234A567018", 11), 587⟩, ⟨decodeRow 12 ("234A5670198", 11), 588⟩, ⟨decodeRow 12 ("34A56701928", 9), 589⟩]))))
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("834A5670129", 11), 588⟩, ⟨decodeRow 12 ("34A56701289", 11), 589⟩, ⟨decodeRow 12 ("4A567012839", 11), 590⟩, ⟨decodeRow 12 ("A5670128349", 11), 591⟩, ⟨decodeRow 12 ("567012834A9", 11), 592⟩, ⟨decodeRow 12 ("67012834A59", 11), 593⟩, ⟨decodeRow 12 ("7012834A569", 11), 594⟩])
                (.leaf [⟨decodeRow 12 ("012834A5679", 11), 595⟩, ⟨decodeRow 12 ("12834A56709", 9), 596⟩, ⟨decodeRow 12 ("912834A5607", 11), 595⟩, ⟨decodeRow 12 ("12834A56097", 11), 596⟩, ⟨decodeRow 12 ("2834A560917", 11), 597⟩, ⟨decodeRow 12 ("834A5609127", 11), 598⟩, ⟨decodeRow 12 ("34A56091287", 11), 599⟩, ⟨decodeRow 12 ("4A560912837", 9), 600⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("74A56091238", 11), 599⟩, ⟨decodeRow 12 ("4A560912378", 11), 600⟩, ⟨decodeRow 12 ("A5609123748", 9), 601⟩, ⟨decodeRow 12 ("8A560912347", 11), 600⟩, ⟨decodeRow 12 ("A5609123487", 11), 601⟩, ⟨decodeRow 12 ("560912348A7", 11), 602⟩, ⟨decodeRow 12 ("60912348A57", 9), 603⟩, ⟨decodeRow 12 ("7609123485A", 9), 602⟩])
                (.leaf [⟨decodeRow 12 ("A7609123458", 11), 601⟩, ⟨decodeRow 12 ("760912345A8", 11), 602⟩, ⟨decodeRow 12 ("60912345A78", 11), 603⟩, ⟨decodeRow 12 ("0912345A768", 11), 604⟩, ⟨decodeRow 12 ("912345A7608", 11), 605⟩, ⟨decodeRow 12 ("12345A76098", 11), 606⟩, ⟨decodeRow 12 ("2345A760918", 9), 607⟩, ⟨decodeRow 12 ("82345A76019", 11), 606⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("2345A760189", 11), 607⟩, ⟨decodeRow 12 ("345A7601829", 11), 608⟩, ⟨decodeRow 12 ("45A76018239", 11), 609⟩, ⟨decodeRow 12 ("5A760182349", 11), 610⟩, ⟨decodeRow 12 ("A7601823459", 11), 611⟩, ⟨decodeRow 12 ("760182345A9", 11), 612⟩, ⟨decodeRow 12 ("60182345A79", 11), 613⟩, ⟨decodeRow 12 ("0182345A769", 9), 614⟩])
                (.leaf [⟨decodeRow 12 ("90182345A67", 11), 613⟩, ⟨decodeRow 12 ("0182345A697", 11), 614⟩, ⟨decodeRow 12 ("182345A6907", 11), 615⟩, ⟨decodeRow 12 ("82345A69017", 11), 616⟩, ⟨decodeRow 12 ("2345A690187", 11), 617⟩, ⟨decodeRow 12 ("345A6901827", 9), 618⟩, ⟨decodeRow 12 ("7345A690128", 11), 617⟩, ⟨decodeRow 12 ("345A6901278", 11), 618⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("45A69012738", 9), 619⟩, ⟨decodeRow 12 ("845A6901237", 11), 618⟩, ⟨decodeRow 12 ("45A69012387", 11), 619⟩, ⟨decodeRow 12 ("5A690123847", 9), 620⟩, ⟨decodeRow 12 ("75A69012348", 11), 619⟩, ⟨decodeRow 12 ("5A690123478", 11), 620⟩, ⟨decodeRow 12 ("A6901234758", 11), 621⟩, ⟨decodeRow 12 ("690123475A8", 11), 622⟩])
                (.leaf [⟨decodeRow 12 ("90123475A68", 11), 623⟩, ⟨decodeRow 12 ("0123475A698", 11), 624⟩, ⟨decodeRow 12 ("123475A6908", 9), 625⟩, ⟨decodeRow 12 ("8123475A609", 11), 624⟩, ⟨decodeRow 12 ("123475A6089", 11), 625⟩, ⟨decodeRow 12 ("23475A60819", 11), 626⟩, ⟨decodeRow 12 ("3475A608129", 11), 627⟩, ⟨decodeRow 12 ("475A6081239", 11), 628⟩])))))
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("75A60812349", 11), 629⟩, ⟨decodeRow 12 ("5A608123479", 11), 630⟩, ⟨decodeRow 12 ("A6081234759", 9), 631⟩, ⟨decodeRow 12 ("9A608123457", 11), 630⟩, ⟨decodeRow 12 ("A6081234597", 11), 631⟩, ⟨decodeRow 12 ("608123459A7", 11), 632⟩, ⟨decodeRow 12 ("08123459A67", 11), 633⟩])
                (.leaf [⟨decodeRow 12 ("8123459A607", 11), 634⟩, ⟨decodeRow 12 ("123459A6087", 11), 635⟩, ⟨decodeRow 12 ("23459A60817", 9), 636⟩, ⟨decodeRow 12 ("723459A6018", 11), 635⟩, ⟨decodeRow 12 ("23459A60178", 11), 636⟩, ⟨decodeRow 12 ("3459A601728", 9), 637⟩, ⟨decodeRow 12 ("83459A60127", 11), 636⟩, ⟨decodeRow 12 ("3459A601287", 11), 637⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("459A6012837", 9), 638⟩, ⟨decodeRow 12 ("7459A601238", 11), 637⟩, ⟨decodeRow 12 ("459A6012378", 11), 638⟩, ⟨decodeRow 12 ("59A60123748", 11), 639⟩, ⟨decodeRow 12 ("9A601237458", 11), 640⟩, ⟨decodeRow 12 ("A6012374598", 11), 641⟩, ⟨decodeRow 12 ("601237459A8", 11), 642⟩, ⟨decodeRow 12 ("01237459A68", 9), 643⟩])
                (.leaf [⟨decodeRow 12 ("8012374596A", 9), 642⟩, ⟨decodeRow 12 ("A8012374569", 11), 641⟩, ⟨decodeRow 12 ("801237456A9", 11), 642⟩, ⟨decodeRow 12 ("01237456A89", 11), 643⟩, ⟨decodeRow 12 ("1237456A809", 11), 644⟩, ⟨decodeRow 12 ("237456A8019", 11), 645⟩, ⟨decodeRow 12 ("37456A80129", 11), 646⟩, ⟨decodeRow 12 ("7456A801239", 11), 647⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("456A8012379", 11), 648⟩, ⟨decodeRow 12 ("56A80123749", 9), 649⟩, ⟨decodeRow 12 ("956A8012347", 11), 648⟩, ⟨decodeRow 12 ("56A80123497", 11), 649⟩, ⟨decodeRow 12 ("6A801234957", 11), 650⟩, ⟨decodeRow 12 ("A8012349567", 11), 651⟩, ⟨decodeRow 12 ("801234956A7", 11), 652⟩, ⟨decodeRow 12 ("01234956A87", 11), 653⟩])
                (.leaf [⟨decodeRow 12 ("1234956A807", 9), 654⟩, ⟨decodeRow 12 ("71234956A08", 11), 653⟩, ⟨decodeRow 12 ("1234956A078", 9), 654⟩, ⟨decodeRow 12 ("81234956A70", 9), 653⟩, ⟨decodeRow 12 ("0812349567A", 11), 652⟩, ⟨decodeRow 12 ("8123495670A", 11), 653⟩, ⟨decodeRow 12 ("1234956708A", 11), 654⟩, ⟨decodeRow 12 ("2349567081A", 9), 655⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A2349567018", 11), 654⟩, ⟨decodeRow 12 ("234956701A8", 9), 655⟩, ⟨decodeRow 12 ("823495670A1", 9), 654⟩, ⟨decodeRow 12 ("182349567A0", 9), 653⟩, ⟨decodeRow 12 ("018234956A7", 11), 652⟩, ⟨decodeRow 12 ("18234956A07", 11), 653⟩, ⟨decodeRow 12 ("8234956A017", 11), 654⟩, ⟨decodeRow 12 ("234956A0187", 11), 655⟩])
                (.leaf [⟨decodeRow 12 ("34956A01827", 9), 656⟩, ⟨decodeRow 12 ("734956A0128", 11), 655⟩, ⟨decodeRow 12 ("34956A01278", 11), 656⟩, ⟨decodeRow 12 ("4956A012738", 11), 657⟩, ⟨decodeRow 12 ("956A0127348", 11), 658⟩, ⟨decodeRow 12 ("56A01273498", 11), 659⟩, ⟨decodeRow 12 ("6A012734958", 9), 660⟩, ⟨decodeRow 12 ("86A01273459", 11), 659⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("6A012734589", 11), 660⟩, ⟨decodeRow 12 ("A0127345869", 11), 661⟩, ⟨decodeRow 12 ("012734586A9", 11), 662⟩, ⟨decodeRow 12 ("12734586A09", 11), 663⟩, ⟨decodeRow 12 ("2734586A019", 11), 664⟩, ⟨decodeRow 12 ("734586A0129", 11), 665⟩, ⟨decodeRow 12 ("34586A01279", 11), 666⟩, ⟨decodeRow 12 ("4586A012739", 9), 667⟩])
                (.leaf [⟨decodeRow 12 ("94586A01237", 11), 666⟩, ⟨decodeRow 12 ("4586A012397", 11), 667⟩, ⟨decodeRow 12 ("586A0123947", 11), 668⟩, ⟨decodeRow 12 ("86A01239457", 11), 669⟩, ⟨decodeRow 12 ("6A012394587", 11), 670⟩, ⟨decodeRow 12 ("A0123945867", 9), 671⟩, ⟨decodeRow 12 ("7A012394568", 11), 670⟩, ⟨decodeRow 12 ("A0123945678", 11), 671⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("012394567A8", 11), 672⟩, ⟨decodeRow 12 ("12394567A08", 9), 673⟩, ⟨decodeRow 12 ("8123945670A", 9), 672⟩, ⟨decodeRow 12 ("A8123945607", 11), 671⟩, ⟨decodeRow 12 ("812394560A7", 11), 672⟩, ⟨decodeRow 12 ("12394560A87", 11), 673⟩, ⟨decodeRow 12 ("2394560A817", 9), 674⟩, ⟨decodeRow 12 ("72394560A18", 11), 673⟩])
                (.leaf [⟨decodeRow 12 ("2394560A178", 11), 674⟩, ⟨decodeRow 12 ("394560A1728", 11), 675⟩, ⟨decodeRow 12 ("94560A17238", 11), 676⟩, ⟨decodeRow 12 ("4560A172398", 11), 677⟩, ⟨decodeRow 12 ("560A1723948", 9), 678⟩, ⟨decodeRow 12 ("8560A172349", 11), 677⟩, ⟨decodeRow 12 ("560A1723489", 11), 678⟩, ⟨decodeRow 12 ("60A17234859", 11), 679⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("0A172348569", 11), 680⟩, ⟨decodeRow 12 ("A1723485609", 11), 681⟩, ⟨decodeRow 12 ("172348560A9", 11), 682⟩, ⟨decodeRow 12 ("72348560A19", 11), 683⟩, ⟨decodeRow 12 ("2348560A179", 11), 684⟩, ⟨decodeRow 12 ("348560A1729", 9), 685⟩, ⟨decodeRow 12 ("9348560A127", 11), 684⟩, ⟨decodeRow 12 ("348560A1297", 11), 685⟩])
                (.leaf [⟨decodeRow 12 ("48560A12937", 11), 686⟩, ⟨decodeRow 12 ("8560A129347", 11), 687⟩, ⟨decodeRow 12 ("560A1293487", 11), 688⟩, ⟨decodeRow 12 ("60A12934857", 9), 689⟩, ⟨decodeRow 12 ("760A1293458", 11), 688⟩, ⟨decodeRow 12 ("60A12934578", 11), 689⟩, ⟨decodeRow 12 ("0A129345768", 11), 690⟩, ⟨decodeRow 12 ("A1293457608", 11), 691⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("129345760A8", 9), 692⟩, ⟨decodeRow 12 ("812934576A0", 9), 691⟩, ⟨decodeRow 12 ("081293457A6", 9), 690⟩, ⟨decodeRow 12 ("608129345A7", 11), 689⟩, ⟨decodeRow 12 ("08129345A67", 9), 690⟩, ⟨decodeRow 12 ("7081293456A", 11), 689⟩, ⟨decodeRow 12 ("0812934567A", 11), 690⟩, ⟨decodeRow 12 ("8129345670A", 11), 691⟩])
                (.leaf [⟨decodeRow 12 ("1293456708A", 9), 692⟩, ⟨decodeRow 12 ("A1293456780", 9), 691⟩, ⟨decodeRow 12 ("0A129345687", 11), 690⟩, ⟨decodeRow 12 ("A1293456807", 9), 691⟩, ⟨decodeRow 12 ("7A129345608", 11), 690⟩, ⟨decodeRow 12 ("A1293456078", 11), 691⟩, ⟨decodeRow 12 ("129345607A8", 11), 692⟩, ⟨decodeRow 12 ("29345607A18", 11), 693⟩]))))))
      (.branch 127
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("9345607A128", 11), 694⟩, ⟨decodeRow 12 ("345607A1298", 11), 695⟩, ⟨decodeRow 12 ("45607A12938", 9), 696⟩, ⟨decodeRow 12 ("845607A1239", 11), 695⟩, ⟨decodeRow 12 ("45607A12389", 11), 696⟩, ⟨decodeRow 12 ("5607A123849", 11), 697⟩, ⟨decodeRow 12 ("607A1238459", 11), 698⟩])
                (.leaf [⟨decodeRow 12 ("07A12384569", 11), 699⟩, ⟨decodeRow 12 ("7A123845609", 11), 700⟩, ⟨decodeRow 12 ("A1238456079", 11), 701⟩, ⟨decodeRow 12 ("123845607A9", 11), 702⟩, ⟨decodeRow 12 ("23845607A19", 9), 703⟩, ⟨decodeRow 12 ("9238456071A", 9), 702⟩, ⟨decodeRow 12 ("A9238456017", 11), 701⟩, ⟨decodeRow 12 ("923845601A7", 11), 702⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("23845601A97", 11), 703⟩, ⟨decodeRow 12 ("3845601A927", 11), 704⟩, ⟨decodeRow 12 ("845601A9237", 11), 705⟩, ⟨decodeRow 12 ("45601A92387", 11), 706⟩, ⟨decodeRow 12 ("5601A923847", 9), 707⟩, ⟨decodeRow 12 ("75601A92348", 11), 706⟩, ⟨decodeRow 12 ("5601A923478", 11), 707⟩, ⟨decodeRow 12 ("601A9234758", 9), 708⟩])
                (.leaf [⟨decodeRow 12 ("8601A923457", 11), 707⟩, ⟨decodeRow 12 ("601A9234587", 11), 708⟩, ⟨decodeRow 12 ("01A92345867", 9), 709⟩, ⟨decodeRow 12 ("701A9234568", 11), 708⟩, ⟨decodeRow 12 ("01A92345678", 11), 709⟩, ⟨decodeRow 12 ("1A923456708", 11), 710⟩, ⟨decodeRow 12 ("A9234567018", 11), 711⟩, ⟨decodeRow 12 ("923456701A8", 11), 712⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("23456701A98", 11), 713⟩, ⟨decodeRow 12 ("3456701A928", 9), 714⟩, ⟨decodeRow 12 ("83456701A29", 11), 713⟩, ⟨decodeRow 12 ("3456701A289", 11), 714⟩, ⟨decodeRow 12 ("456701A2839", 11), 715⟩, ⟨decodeRow 12 ("56701A28349", 11), 716⟩, ⟨decodeRow 12 ("6701A283459", 11), 717⟩, ⟨decodeRow 12 ("701A2834569", 11), 718⟩])
                (.leaf [⟨decodeRow 12 ("01A28345679", 11), 719⟩, ⟨decodeRow 12 ("1A283456709", 9), 720⟩, ⟨decodeRow 12 ("91A28345607", 11), 719⟩, ⟨decodeRow 12 ("1A283456097", 11), 720⟩, ⟨decodeRow 12 ("A2834560917", 11), 721⟩, ⟨decodeRow 12 ("283456091A7", 11), 722⟩, ⟨decodeRow 12 ("83456091A27", 11), 723⟩, ⟨decodeRow 12 ("3456091A287", 11), 724⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("456091A2837", 9), 725⟩, ⟨decodeRow 12 ("7456091A238", 11), 724⟩, ⟨decodeRow 12 ("456091A2378", 11), 725⟩, ⟨decodeRow 12 ("56091A23748", 9), 726⟩, ⟨decodeRow 12 ("856091A2347", 11), 725⟩, ⟨decodeRow 12 ("56091A23487", 11), 726⟩, ⟨decodeRow 12 ("6091A234857", 9), 727⟩, ⟨decodeRow 12 ("76091A23458", 11), 726⟩])
                (.leaf [⟨decodeRow 12 ("6091A234578", 11), 727⟩, ⟨decodeRow 12 ("091A2345768", 11), 728⟩, ⟨decodeRow 12 ("91A23457608", 11), 729⟩, ⟨decodeRow 12 ("1A234576098", 11), 730⟩, ⟨decodeRow 12 ("A2345760918", 9), 731⟩, ⟨decodeRow 12 ("8A234576019", 11), 730⟩, ⟨decodeRow 12 ("A2345760189", 11), 731⟩, ⟨decodeRow 12 ("234576018A9", 11), 732⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("34576018A29", 11), 733⟩, ⟨decodeRow 12 ("4576018A239", 11), 734⟩, ⟨decodeRow 12 ("576018A2349", 11), 735⟩, ⟨decodeRow 12 ("76018A23459", 11), 736⟩, ⟨decodeRow 12 ("6018A234579", 11), 737⟩, ⟨decodeRow 12 ("018A2345769", 9), 738⟩, ⟨decodeRow 12 ("9018A234567", 11), 737⟩, ⟨decodeRow 12 ("018A2345697", 11), 738⟩])
                (.leaf [⟨decodeRow 12 ("18A23456907", 11), 739⟩, ⟨decodeRow 12 ("8A234569017", 11), 740⟩, ⟨decodeRow 12 ("A2345690187", 11), 741⟩, ⟨decodeRow 12 ("234569018A7", 11), 742⟩, ⟨decodeRow 12 ("34569018A27", 9), 743⟩, ⟨decodeRow 12 ("7345690182A", 9), 742⟩, ⟨decodeRow 12 ("A7345690128", 11), 741⟩, ⟨decodeRow 12 ("734569012A8", 11), 742⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("34569012A78", 11), 743⟩, ⟨decodeRow 12 ("4569012A738", 9), 744⟩, ⟨decodeRow 12 ("84569012A37", 11), 743⟩, ⟨decodeRow 12 ("4569012A387", 9), 744⟩, ⟨decodeRow 12 ("74569012A83", 9), 743⟩, ⟨decodeRow 12 ("3745690128A", 11), 742⟩, ⟨decodeRow 12 ("7456901283A", 11), 743⟩, ⟨decodeRow 12 ("4569012837A", 11), 744⟩])
                (.leaf [⟨decodeRow 12 ("5690128374A", 9), 745⟩, ⟨decodeRow 12 ("A5690128347", 11), 744⟩, ⟨decodeRow 12 ("569012834A7", 9), 745⟩, ⟨decodeRow 12 ("756901283A4", 9), 744⟩, ⟨decodeRow 12 ("475690128A3", 9), 743⟩, ⟨decodeRow 12 ("347569012A8", 11), 742⟩, ⟨decodeRow 12 ("47569012A38", 11), 743⟩, ⟨decodeRow 12 ("7569012A348", 11), 744⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("569012A3478", 11), 745⟩, ⟨decodeRow 12 ("69012A34758", 11), 746⟩, ⟨decodeRow 12 ("9012A347568", 11), 747⟩, ⟨decodeRow 12 ("012A3475698", 11), 748⟩, ⟨decodeRow 12 ("12A34756908", 9), 749⟩, ⟨decodeRow 12 ("812A3475609", 11), 748⟩, ⟨decodeRow 12 ("12A34756089", 11), 749⟩, ⟨decodeRow 12 ("2A347560819", 11), 750⟩])
                (.leaf [⟨decodeRow 12 ("A3475608129", 11), 751⟩, ⟨decodeRow 12 ("347560812A9", 11), 752⟩, ⟨decodeRow 12 ("47560812A39", 11), 753⟩, ⟨decodeRow 12 ("7560812A349", 11), 754⟩, ⟨decodeRow 12 ("560812A3479", 11), 755⟩, ⟨decodeRow 12 ("60812A34759", 9), 756⟩, ⟨decodeRow 12 ("960812A3457", 11), 755⟩, ⟨decodeRow 12 ("60812A34597", 11), 756⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("0812A345967", 11), 757⟩, ⟨decodeRow 12 ("812A3459607", 11), 758⟩, ⟨decodeRow 12 ("12A34596087", 11), 759⟩, ⟨decodeRow 12 ("2A345960817", 9), 760⟩, ⟨decodeRow 12 ("72A34596018", 11), 759⟩, ⟨decodeRow 12 ("2A345960178", 11), 760⟩, ⟨decodeRow 12 ("A3459601728", 9), 761⟩, ⟨decodeRow 12 ("8A345960127", 11), 760⟩])
                (.leaf [⟨decodeRow 12 ("A3459601287", 11), 761⟩, ⟨decodeRow 12 ("345960128A7", 11), 762⟩, ⟨decodeRow 12 ("45960128A37", 9), 763⟩, ⟨decodeRow 12 ("7459601283A", 9), 762⟩, ⟨decodeRow 12 ("A7459601238", 11), 761⟩, ⟨decodeRow 12 ("745960123A8", 11), 762⟩, ⟨decodeRow 12 ("45960123A78", 11), 763⟩, ⟨decodeRow 12 ("5960123A748", 11), 764⟩])))))
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("960123A7458", 11), 765⟩, ⟨decodeRow 12 ("60123A74598", 11), 766⟩, ⟨decodeRow 12 ("0123A745968", 9), 767⟩, ⟨decodeRow 12 ("80123A74569", 11), 766⟩, ⟨decodeRow 12 ("0123A745689", 11), 767⟩, ⟨decodeRow 12 ("123A7456809", 11), 768⟩, ⟨decodeRow 12 ("23A74568019", 11), 769⟩])
                (.leaf [⟨decodeRow 12 ("3A745680129", 11), 770⟩, ⟨decodeRow 12 ("A7456801239", 11), 771⟩, ⟨decodeRow 12 ("745680123A9", 11), 772⟩, ⟨decodeRow 12 ("45680123A79", 11), 773⟩, ⟨decodeRow 12 ("5680123A749", 9), 774⟩, ⟨decodeRow 12 ("95680123A47", 11), 773⟩, ⟨decodeRow 12 ("5680123A497", 11), 774⟩, ⟨decodeRow 12 ("680123A4957", 11), 775⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("80123A49567", 11), 776⟩, ⟨decodeRow 12 ("0123A495687", 11), 777⟩, ⟨decodeRow 12 ("123A4956807", 9), 778⟩, ⟨decodeRow 12 ("7123A495608", 11), 777⟩, ⟨decodeRow 12 ("123A4956078", 11), 778⟩, ⟨decodeRow 12 ("23A49560718", 9), 779⟩, ⟨decodeRow 12 ("823A4956017", 11), 778⟩, ⟨decodeRow 12 ("23A49560187", 11), 779⟩])
                (.leaf [⟨decodeRow 12 ("3A495601827", 9), 780⟩, ⟨decodeRow 12 ("73A49560128", 11), 779⟩, ⟨decodeRow 12 ("3A495601278", 11), 780⟩, ⟨decodeRow 12 ("A4956012738", 11), 781⟩, ⟨decodeRow 12 ("495601273A8", 11), 782⟩, ⟨decodeRow 12 ("95601273A48", 11), 783⟩, ⟨decodeRow 12 ("5601273A498", 11), 784⟩, ⟨decodeRow 12 ("601273A4958", 9), 785⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("8601273A459", 11), 784⟩, ⟨decodeRow 12 ("601273A4589", 11), 785⟩, ⟨decodeRow 12 ("01273A45869", 11), 786⟩, ⟨decodeRow 12 ("1273A458609", 11), 787⟩, ⟨decodeRow 12 ("273A4586019", 11), 788⟩, ⟨decodeRow 12 ("73A45860129", 11), 789⟩, ⟨decodeRow 12 ("3A458601279", 11), 790⟩, ⟨decodeRow 12 ("A4586012739", 9), 791⟩])
                (.leaf [⟨decodeRow 12 ("9A458601237", 11), 790⟩, ⟨decodeRow 12 ("A4586012397", 11), 791⟩, ⟨decodeRow 12 ("458601239A7", 11), 792⟩, ⟨decodeRow 12 ("58601239A47", 11), 793⟩, ⟨decodeRow 12 ("8601239A457", 11), 794⟩, ⟨decodeRow 12 ("601239A4587", 11), 795⟩, ⟨decodeRow 12 ("01239A45867", 9), 796⟩, ⟨decodeRow 12 ("701239A4568", 11), 795⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("01239A45678", 11), 796⟩, ⟨decodeRow 12 ("1239A456708", 9), 797⟩, ⟨decodeRow 12 ("81239A45607", 11), 796⟩, ⟨decodeRow 12 ("1239A456087", 11), 797⟩, ⟨decodeRow 12 ("239A4560817", 9), 798⟩, ⟨decodeRow 12 ("7239A456018", 11), 797⟩, ⟨decodeRow 12 ("239A4560178", 11), 798⟩, ⟨decodeRow 12 ("39A45601728", 11), 799⟩])
                (.leaf [⟨decodeRow 12 ("9A456017238", 11), 800⟩, ⟨decodeRow 12 ("A4560172398", 11), 801⟩, ⟨decodeRow 12 ("456017239A8", 11), 802⟩, ⟨decodeRow 12 ("56017239A48", 9), 803⟩, ⟨decodeRow 12 ("8560172394A", 9), 802⟩, ⟨decodeRow 12 ("A8560172349", 11), 801⟩, ⟨decodeRow 12 ("856017234A9", 11), 802⟩, ⟨decodeRow 12 ("56017234A89", 11), 803⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("6017234A859", 11), 804⟩, ⟨decodeRow 12 ("017234A8569", 11), 805⟩, ⟨decodeRow 12 ("17234A85609", 11), 806⟩, ⟨decodeRow 12 ("7234A856019", 11), 807⟩, ⟨decodeRow 12 ("234A8560179", 11), 808⟩, ⟨decodeRow 12 ("34A85601729", 9), 809⟩, ⟨decodeRow 12 ("934A8560127", 11), 808⟩, ⟨decodeRow 12 ("34A85601297", 11), 809⟩])
                (.leaf [⟨decodeRow 12 ("4A856012937", 11), 810⟩, ⟨decodeRow 12 ("A8560129347", 11), 811⟩, ⟨decodeRow 12 ("856012934A7", 11), 812⟩, ⟨decodeRow 12 ("56012934A87", 11), 813⟩, ⟨decodeRow 12 ("6012934A857", 9), 814⟩, ⟨decodeRow 12 ("76012934A58", 11), 813⟩, ⟨decodeRow 12 ("6012934A578", 9), 814⟩, ⟨decodeRow 12 ("86012934A75", 9), 813⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("5860129347A", 11), 812⟩, ⟨decodeRow 12 ("8601293475A", 11), 813⟩, ⟨decodeRow 12 ("6012934758A", 11), 814⟩, ⟨decodeRow 12 ("0129347586A", 9), 815⟩, ⟨decodeRow 12 ("A0129347568", 11), 814⟩, ⟨decodeRow 12 ("012934756A8", 9), 815⟩, ⟨decodeRow 12 ("801293475A6", 9), 814⟩, ⟨decodeRow 12 ("680129347A5", 9), 813⟩])
                (.leaf [⟨decodeRow 12 ("568012934A7", 11), 812⟩, ⟨decodeRow 12 ("68012934A57", 11), 813⟩, ⟨decodeRow 12 ("8012934A567", 11), 814⟩, ⟨decodeRow 12 ("012934A5687", 11), 815⟩, ⟨decodeRow 12 ("12934A56807", 9), 816⟩, ⟨decodeRow 12 ("712934A5608", 11), 815⟩, ⟨decodeRow 12 ("12934A56078", 11), 816⟩, ⟨decodeRow 12 ("2934A560718", 11), 817⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("934A5607128", 11), 818⟩, ⟨decodeRow 12 ("34A56071298", 11), 819⟩, ⟨decodeRow 12 ("4A560712938", 9), 820⟩, ⟨decodeRow 12 ("84A56071239", 11), 819⟩, ⟨decodeRow 12 ("4A560712389", 11), 820⟩, ⟨decodeRow 12 ("A5607123849", 11), 821⟩, ⟨decodeRow 12 ("560712384A9", 11), 822⟩, ⟨decodeRow 12 ("60712384A59", 11), 823⟩])
                (.leaf [⟨decodeRow 12 ("0712384A569", 11), 824⟩, ⟨decodeRow 12 ("712384A5609", 11), 825⟩, ⟨decodeRow 12 ("12384A56079", 11), 826⟩, ⟨decodeRow 12 ("2384A560719", 9), 827⟩, ⟨decodeRow 12 ("92384A56017", 11), 826⟩, ⟨decodeRow 12 ("2384A560197", 11), 827⟩, ⟨decodeRow 12 ("384A5601927", 11), 828⟩, ⟨decodeRow 12 ("84A56019237", 11), 829⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("4A560192387", 11), 830⟩, ⟨decodeRow 12 ("A5601923847", 9), 831⟩, ⟨decodeRow 12 ("7A560192348", 11), 830⟩, ⟨decodeRow 12 ("A5601923478", 11), 831⟩, ⟨decodeRow 12 ("560192347A8", 11), 832⟩, ⟨decodeRow 12 ("60192347A58", 9), 833⟩, ⟨decodeRow 12 ("8601923475A", 9), 832⟩, ⟨decodeRow 12 ("A8601923457", 11), 831⟩])
                (.leaf [⟨decodeRow 12 ("860192345A7", 11), 832⟩, ⟨decodeRow 12 ("60192345A87", 11), 833⟩, ⟨decodeRow 12 ("0192345A867", 9), 834⟩, ⟨decodeRow 12 ("70192345A68", 11), 833⟩, ⟨decodeRow 12 ("0192345A678", 11), 834⟩, ⟨decodeRow 12 ("192345A6708", 11), 835⟩, ⟨decodeRow 12 ("92345A67018", 11), 836⟩, ⟨decodeRow 12 ("2345A670198", 11), 837⟩])))))))
    (.branch 254
      (.branch 127
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("345A6701928", 9), 838⟩, ⟨decodeRow 12 ("8345A670129", 11), 837⟩, ⟨decodeRow 12 ("345A6701289", 11), 838⟩, ⟨decodeRow 12 ("45A67012839", 11), 839⟩, ⟨decodeRow 12 ("5A670128349", 11), 840⟩, ⟨decodeRow 12 ("A6701283459", 11), 841⟩, ⟨decodeRow 12 ("670128345A9", 11), 842⟩])
                (.leaf [⟨decodeRow 12 ("70128345A69", 11), 843⟩, ⟨decodeRow 12 ("0128345A679", 11), 844⟩, ⟨decodeRow 12 ("128345A6709", 9), 845⟩, ⟨decodeRow 12 ("9128345A607", 11), 844⟩, ⟨decodeRow 12 ("128345A6097", 11), 845⟩, ⟨decodeRow 12 ("28345A60917", 11), 846⟩, ⟨decodeRow 12 ("8345A609127", 11), 847⟩, ⟨decodeRow 12 ("345A6091287", 11), 848⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("45A60912837", 9), 849⟩, ⟨decodeRow 12 ("745A6091238", 11), 848⟩, ⟨decodeRow 12 ("45A60912378", 11), 849⟩, ⟨decodeRow 12 ("5A609123748", 11), 850⟩, ⟨decodeRow 12 ("A6091237458", 11), 851⟩, ⟨decodeRow 12 ("609123745A8", 9), 852⟩, ⟨decodeRow 12 ("860912374A5", 9), 851⟩, ⟨decodeRow 12 ("586091237A4", 9), 850⟩])
                (.leaf [⟨decodeRow 12 ("458609123A7", 11), 849⟩, ⟨decodeRow 12 ("58609123A47", 9), 850⟩, ⟨decodeRow 12 ("7586091234A", 11), 849⟩, ⟨decodeRow 12 ("5860912347A", 11), 850⟩, ⟨decodeRow 12 ("8609123475A", 11), 851⟩, ⟨decodeRow 12 ("6091234758A", 9), 852⟩, ⟨decodeRow 12 ("A6091234785", 9), 851⟩, ⟨decodeRow 12 ("5A609123487", 11), 850⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A6091234857", 9), 851⟩, ⟨decodeRow 12 ("7A609123458", 11), 850⟩, ⟨decodeRow 12 ("A6091234578", 11), 851⟩, ⟨decodeRow 12 ("609123457A8", 11), 852⟩, ⟨decodeRow 12 ("09123457A68", 11), 853⟩, ⟨decodeRow 12 ("9123457A608", 11), 854⟩, ⟨decodeRow 12 ("123457A6098", 11), 855⟩, ⟨decodeRow 12 ("23457A60918", 9), 856⟩])
                (.leaf [⟨decodeRow 12 ("823457A6019", 11), 855⟩, ⟨decodeRow 12 ("23457A60189", 11), 856⟩, ⟨decodeRow 12 ("3457A601829", 11), 857⟩, ⟨decodeRow 12 ("457A6018239", 11), 858⟩, ⟨decodeRow 12 ("57A60182349", 11), 859⟩, ⟨decodeRow 12 ("7A601823459", 11), 860⟩, ⟨decodeRow 12 ("A6018234579", 11), 861⟩, ⟨decodeRow 12 ("601823457A9", 11), 862⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("01823457A69", 9), 863⟩, ⟨decodeRow 12 ("9018234576A", 9), 862⟩, ⟨decodeRow 12 ("A9018234567", 11), 861⟩, ⟨decodeRow 12 ("901823456A7", 11), 862⟩, ⟨decodeRow 12 ("01823456A97", 11), 863⟩, ⟨decodeRow 12 ("1823456A907", 11), 864⟩, ⟨decodeRow 12 ("823456A9017", 11), 865⟩, ⟨decodeRow 12 ("23456A90187", 11), 866⟩])
                (.leaf [⟨decodeRow 12 ("3456A901827", 9), 867⟩, ⟨decodeRow 12 ("73456A90128", 11), 866⟩, ⟨decodeRow 12 ("3456A901278", 11), 867⟩, ⟨decodeRow 12 ("456A9012738", 9), 868⟩, ⟨decodeRow 12 ("8456A901237", 11), 867⟩, ⟨decodeRow 12 ("456A9012387", 11), 868⟩, ⟨decodeRow 12 ("56A90123847", 9), 869⟩, ⟨decodeRow 12 ("756A9012348", 11), 868⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("56A90123478", 11), 869⟩, ⟨decodeRow 12 ("6A901234758", 11), 870⟩, ⟨decodeRow 12 ("A9012347568", 11), 871⟩, ⟨decodeRow 12 ("901234756A8", 11), 872⟩, ⟨decodeRow 12 ("01234756A98", 11), 873⟩, ⟨decodeRow 12 ("1234756A908", 9), 874⟩, ⟨decodeRow 12 ("81234756A09", 11), 873⟩, ⟨decodeRow 12 ("1234756A089", 11), 874⟩])
                (.leaf [⟨decodeRow 12 ("234756A0819", 11), 875⟩, ⟨decodeRow 12 ("34756A08129", 11), 876⟩, ⟨decodeRow 12 ("4756A081239", 11), 877⟩, ⟨decodeRow 12 ("756A0812349", 11), 878⟩, ⟨decodeRow 12 ("56A08123479", 11), 879⟩, ⟨decodeRow 12 ("6A081234759", 9), 880⟩, ⟨decodeRow 12 ("96A08123457", 11), 879⟩, ⟨decodeRow 12 ("6A081234597", 11), 880⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A0812345967", 11), 881⟩, ⟨decodeRow 12 ("081234596A7", 11), 882⟩, ⟨decodeRow 12 ("81234596A07", 11), 883⟩, ⟨decodeRow 12 ("1234596A087", 11), 884⟩, ⟨decodeRow 12 ("234596A0817", 9), 885⟩, ⟨decodeRow 12 ("7234596A018", 11), 884⟩, ⟨decodeRow 12 ("234596A0178", 11), 885⟩, ⟨decodeRow 12 ("34596A01728", 9), 886⟩])
                (.leaf [⟨decodeRow 12 ("834596A0127", 11), 885⟩, ⟨decodeRow 12 ("34596A01287", 11), 886⟩, ⟨decodeRow 12 ("4596A012837", 9), 887⟩, ⟨decodeRow 12 ("74596A01238", 11), 886⟩, ⟨decodeRow 12 ("4596A012378", 11), 887⟩, ⟨decodeRow 12 ("596A0123748", 11), 888⟩, ⟨decodeRow 12 ("96A01237458", 11), 889⟩, ⟨decodeRow 12 ("6A012374598", 11), 890⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("A0123745968", 9), 891⟩, ⟨decodeRow 12 ("8A012374569", 11), 890⟩, ⟨decodeRow 12 ("A0123745689", 11), 891⟩, ⟨decodeRow 12 ("012374568A9", 11), 892⟩, ⟨decodeRow 12 ("12374568A09", 11), 893⟩, ⟨decodeRow 12 ("2374568A019", 11), 894⟩, ⟨decodeRow 12 ("374568A0129", 11), 895⟩, ⟨decodeRow 12 ("74568A01239", 11), 896⟩])
                (.leaf [⟨decodeRow 12 ("4568A012379", 11), 897⟩, ⟨decodeRow 12 ("568A0123749", 9), 898⟩, ⟨decodeRow 12 ("9568A012347", 11), 897⟩, ⟨decodeRow 12 ("568A0123497", 11), 898⟩, ⟨decodeRow 12 ("68A01234957", 11), 899⟩, ⟨decodeRow 12 ("8A012349567", 11), 900⟩, ⟨decodeRow 12 ("A0123495687", 11), 901⟩, ⟨decodeRow 12 ("012349568A7", 11), 902⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("12349568A07", 9), 903⟩, ⟨decodeRow 12 ("7123495680A", 9), 902⟩, ⟨decodeRow 12 ("A7123495608", 11), 901⟩, ⟨decodeRow 12 ("712349560A8", 11), 902⟩, ⟨decodeRow 12 ("12349560A78", 11), 903⟩, ⟨decodeRow 12 ("2349560A718", 9), 904⟩, ⟨decodeRow 12 ("82349560A17", 11), 903⟩, ⟨decodeRow 12 ("2349560A187", 9), 904⟩])
                (.leaf [⟨decodeRow 12 ("72349560A81", 9), 903⟩, ⟨decodeRow 12 ("1723495608A", 11), 902⟩, ⟨decodeRow 12 ("7234956081A", 11), 903⟩, ⟨decodeRow 12 ("2349560817A", 11), 904⟩, ⟨decodeRow 12 ("3495608172A", 9), 905⟩, ⟨decodeRow 12 ("A3495608127", 11), 904⟩, ⟨decodeRow 12 ("349560812A7", 9), 905⟩, ⟨decodeRow 12 ("734956081A2", 9), 904⟩])))))
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("273495608A1", 9), 903⟩, ⟨decodeRow 12 ("127349560A8", 11), 902⟩, ⟨decodeRow 12 ("27349560A18", 11), 903⟩, ⟨decodeRow 12 ("7349560A128", 11), 904⟩, ⟨decodeRow 12 ("349560A1278", 11), 905⟩, ⟨decodeRow 12 ("49560A12738", 11), 906⟩, ⟨decodeRow 12 ("9560A127348", 11), 907⟩])
                (.leaf [⟨decodeRow 12 ("560A1273498", 11), 908⟩, ⟨decodeRow 12 ("60A12734958", 9), 909⟩, ⟨decodeRow 12 ("860A1273459", 11), 908⟩, ⟨decodeRow 12 ("60A12734589", 11), 909⟩, ⟨decodeRow 12 ("0A127345869", 11), 910⟩, ⟨decodeRow 12 ("A1273458609", 11), 911⟩, ⟨decodeRow 12 ("127345860A9", 11), 912⟩, ⟨decodeRow 12 ("27345860A19", 11), 913⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("7345860A129", 11), 914⟩, ⟨decodeRow 12 ("345860A1279", 11), 915⟩, ⟨decodeRow 12 ("45860A12739", 9), 916⟩, ⟨decodeRow 12 ("945860A1237", 11), 915⟩, ⟨decodeRow 12 ("45860A12397", 11), 916⟩, ⟨decodeRow 12 ("5860A123947", 11), 917⟩, ⟨decodeRow 12 ("860A1239457", 11), 918⟩, ⟨decodeRow 12 ("60A12394587", 11), 919⟩])
                (.leaf [⟨decodeRow 12 ("0A123945867", 9), 920⟩, ⟨decodeRow 12 ("70A12394568", 11), 919⟩, ⟨decodeRow 12 ("0A123945678", 11), 920⟩, ⟨decodeRow 12 ("A1239456708", 9), 921⟩, ⟨decodeRow 12 ("8A123945607", 11), 920⟩, ⟨decodeRow 12 ("A1239456087", 11), 921⟩, ⟨decodeRow 12 ("123945608A7", 11), 922⟩, ⟨decodeRow 12 ("23945608A17", 9), 923⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("7239456081A", 9), 922⟩, ⟨decodeRow 12 ("A7239456018", 11), 921⟩, ⟨decodeRow 12 ("723945601A8", 11), 922⟩, ⟨decodeRow 12 ("23945601A78", 11), 923⟩, ⟨decodeRow 12 ("3945601A728", 11), 924⟩, ⟨decodeRow 12 ("945601A7238", 11), 925⟩, ⟨decodeRow 12 ("45601A72398", 11), 926⟩, ⟨decodeRow 12 ("5601A723948", 9), 927⟩])
                (.leaf [⟨decodeRow 12 ("85601A72349", 11), 926⟩, ⟨decodeRow 12 ("5601A723489", 11), 927⟩, ⟨decodeRow 12 ("601A7234859", 11), 928⟩, ⟨decodeRow 12 ("01A72348569", 11), 929⟩, ⟨decodeRow 12 ("1A723485609", 11), 930⟩, ⟨decodeRow 12 ("A7234856019", 11), 931⟩, ⟨decodeRow 12 ("723485601A9", 11), 932⟩, ⟨decodeRow 12 ("23485601A79", 11), 933⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("3485601A729", 9), 934⟩, ⟨decodeRow 12 ("93485601A27", 11), 933⟩, ⟨decodeRow 12 ("3485601A297", 11), 934⟩, ⟨decodeRow 12 ("485601A2937", 11), 935⟩, ⟨decodeRow 12 ("85601A29347", 11), 936⟩, ⟨decodeRow 12 ("5601A293487", 11), 937⟩, ⟨decodeRow 12 ("601A2934857", 9), 938⟩, ⟨decodeRow 12 ("7601A293458", 11), 937⟩])
                (.leaf [⟨decodeRow 12 ("601A2934578", 11), 938⟩, ⟨decodeRow 12 ("01A29345768", 9), 939⟩, ⟨decodeRow 12 ("801A2934567", 11), 938⟩, ⟨decodeRow 12 ("01A29345687", 11), 939⟩, ⟨decodeRow 12 ("1A293456807", 9), 940⟩, ⟨decodeRow 12 ("71A29345608", 11), 939⟩, ⟨decodeRow 12 ("1A293456078", 11), 940⟩, ⟨decodeRow 12 ("A2934560718", 11), 941⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("293456071A8", 11), 942⟩, ⟨decodeRow 12 ("93456071A28", 11), 943⟩, ⟨decodeRow 12 ("3456071A298", 11), 944⟩, ⟨decodeRow 12 ("456071A2938", 9), 945⟩, ⟨decodeRow 12 ("8456071A239", 11), 944⟩, ⟨decodeRow 12 ("456071A2389", 11), 945⟩, ⟨decodeRow 12 ("56071A23849", 11), 946⟩, ⟨decodeRow 12 ("6071A238459", 11), 947⟩])
                (.leaf [⟨decodeRow 12 ("071A2384569", 11), 948⟩, ⟨decodeRow 12 ("71A23845609", 11), 949⟩, ⟨decodeRow 12 ("1A238456079", 11), 950⟩, ⟨decodeRow 12 ("A2384560719", 9), 951⟩, ⟨decodeRow 12 ("9A238456017", 11), 950⟩, ⟨decodeRow 12 ("A2384560197", 11), 951⟩, ⟨decodeRow 12 ("238456019A7", 11), 952⟩, ⟨decodeRow 12 ("38456019A27", 11), 953⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("8456019A237", 11), 954⟩, ⟨decodeRow 12 ("456019A2387", 11), 955⟩, ⟨decodeRow 12 ("56019A23847", 9), 956⟩, ⟨decodeRow 12 ("756019A2348", 11), 955⟩, ⟨decodeRow 12 ("56019A23478", 11), 956⟩, ⟨decodeRow 12 ("6019A234758", 9), 957⟩, ⟨decodeRow 12 ("86019A23457", 11), 956⟩, ⟨decodeRow 12 ("6019A234587", 11), 957⟩])
                (.leaf [⟨decodeRow 12 ("019A2345867", 9), 958⟩, ⟨decodeRow 12 ("7019A234568", 11), 957⟩, ⟨decodeRow 12 ("019A2345678", 11), 958⟩, ⟨decodeRow 12 ("19A23456708", 11), 959⟩, ⟨decodeRow 12 ("9A234567018", 11), 960⟩, ⟨decodeRow 12 ("A2345670198", 11), 961⟩, ⟨decodeRow 12 ("234567019A8", 11), 962⟩, ⟨decodeRow 12 ("34567019A28", 9), 963⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("8345670192A", 9), 962⟩, ⟨decodeRow 12 ("A8345670129", 11), 961⟩, ⟨decodeRow 12 ("834567012A9", 11), 962⟩, ⟨decodeRow 12 ("34567012A89", 11), 963⟩, ⟨decodeRow 12 ("4567012A839", 11), 964⟩, ⟨decodeRow 12 ("567012A8349", 11), 965⟩, ⟨decodeRow 12 ("67012A83459", 11), 966⟩, ⟨decodeRow 12 ("7012A834569", 11), 967⟩])
                (.leaf [⟨decodeRow 12 ("012A8345679", 11), 968⟩, ⟨decodeRow 12 ("12A83456709", 9), 969⟩, ⟨decodeRow 12 ("912A8345607", 11), 968⟩, ⟨decodeRow 12 ("12A83456097", 11), 969⟩, ⟨decodeRow 12 ("2A834560917", 11), 970⟩, ⟨decodeRow 12 ("A8345609127", 11), 971⟩, ⟨decodeRow 12 ("834560912A7", 11), 972⟩, ⟨decodeRow 12 ("34560912A87", 11), 973⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("4560912A837", 9), 974⟩, ⟨decodeRow 12 ("74560912A38", 11), 973⟩, ⟨decodeRow 12 ("4560912A378", 9), 974⟩, ⟨decodeRow 12 ("84560912A73", 9), 973⟩, ⟨decodeRow 12 ("3845609127A", 11), 972⟩, ⟨decodeRow 12 ("8456091273A", 11), 973⟩, ⟨decodeRow 12 ("4560912738A", 11), 974⟩, ⟨decodeRow 12 ("5609127384A", 9), 975⟩])
                (.leaf [⟨decodeRow 12 ("A5609127348", 11), 974⟩, ⟨decodeRow 12 ("560912734A8", 9), 975⟩, ⟨decodeRow 12 ("856091273A4", 9), 974⟩, ⟨decodeRow 12 ("485609127A3", 9), 973⟩, ⟨decodeRow 12 ("348560912A7", 11), 972⟩, ⟨decodeRow 12 ("48560912A37", 11), 973⟩, ⟨decodeRow 12 ("8560912A347", 11), 974⟩, ⟨decodeRow 12 ("560912A3487", 11), 975⟩]))))))
      (.branch 127
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("60912A34857", 9), 976⟩, ⟨decodeRow 12 ("760912A3458", 11), 975⟩, ⟨decodeRow 12 ("60912A34578", 11), 976⟩, ⟨decodeRow 12 ("0912A345768", 11), 977⟩, ⟨decodeRow 12 ("912A3457608", 11), 978⟩, ⟨decodeRow 12 ("12A34576098", 11), 979⟩, ⟨decodeRow 12 ("2A345760918", 9), 980⟩])
                (.leaf [⟨decodeRow 12 ("82A34576019", 11), 979⟩, ⟨decodeRow 12 ("2A345760189", 11), 980⟩, ⟨decodeRow 12 ("A3457601829", 11), 981⟩, ⟨decodeRow 12 ("345760182A9", 11), 982⟩, ⟨decodeRow 12 ("45760182A39", 11), 983⟩, ⟨decodeRow 12 ("5760182A349", 11), 984⟩, ⟨decodeRow 12 ("760182A3459", 11), 985⟩, ⟨decodeRow 12 ("60182A34579", 11), 986⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("0182A345769", 9), 987⟩, ⟨decodeRow 12 ("90182A34567", 11), 986⟩, ⟨decodeRow 12 ("0182A345697", 11), 987⟩, ⟨decodeRow 12 ("182A3456907", 11), 988⟩, ⟨decodeRow 12 ("82A34569017", 11), 989⟩, ⟨decodeRow 12 ("2A345690187", 11), 990⟩, ⟨decodeRow 12 ("A3456901827", 9), 991⟩, ⟨decodeRow 12 ("7A345690128", 11), 990⟩])
                (.leaf [⟨decodeRow 12 ("A3456901278", 11), 991⟩, ⟨decodeRow 12 ("345690127A8", 11), 992⟩, ⟨decodeRow 12 ("45690127A38", 9), 993⟩, ⟨decodeRow 12 ("8456901273A", 9), 992⟩, ⟨decodeRow 12 ("A8456901237", 11), 991⟩, ⟨decodeRow 12 ("845690123A7", 11), 992⟩, ⟨decodeRow 12 ("45690123A87", 11), 993⟩, ⟨decodeRow 12 ("5690123A847", 9), 994⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("75690123A48", 11), 993⟩, ⟨decodeRow 12 ("5690123A478", 11), 994⟩, ⟨decodeRow 12 ("690123A4758", 11), 995⟩, ⟨decodeRow 12 ("90123A47568", 11), 996⟩, ⟨decodeRow 12 ("0123A475698", 11), 997⟩, ⟨decodeRow 12 ("123A4756908", 9), 998⟩, ⟨decodeRow 12 ("8123A475609", 11), 997⟩, ⟨decodeRow 12 ("123A4756089", 11), 998⟩])
                (.leaf [⟨decodeRow 12 ("23A47560819", 11), 999⟩, ⟨decodeRow 12 ("3A475608129", 11), 1000⟩, ⟨decodeRow 12 ("A4756081239", 11), 1001⟩, ⟨decodeRow 12 ("475608123A9", 11), 1002⟩, ⟨decodeRow 12 ("75608123A49", 11), 1003⟩, ⟨decodeRow 12 ("5608123A479", 11), 1004⟩, ⟨decodeRow 12 ("608123A4759", 9), 1005⟩, ⟨decodeRow 12 ("9608123A457", 11), 1004⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("608123A4597", 11), 1005⟩, ⟨decodeRow 12 ("08123A45967", 11), 1006⟩, ⟨decodeRow 12 ("8123A459607", 11), 1007⟩, ⟨decodeRow 12 ("123A4596087", 11), 1008⟩, ⟨decodeRow 12 ("23A45960817", 9), 1009⟩, ⟨decodeRow 12 ("723A4596018", 11), 1008⟩, ⟨decodeRow 12 ("23A45960178", 11), 1009⟩, ⟨decodeRow 12 ("3A459601728", 11), 1010⟩])
                (.leaf [⟨decodeRow 12 ("A4596017238", 11), 1011⟩, ⟨decodeRow 12 ("459601723A8", 9), 1012⟩, ⟨decodeRow 12 ("845960172A3", 9), 1011⟩, ⟨decodeRow 12 ("384596017A2", 9), 1010⟩, ⟨decodeRow 12 ("238459601A7", 11), 1009⟩, ⟨decodeRow 12 ("38459601A27", 9), 1010⟩, ⟨decodeRow 12 ("7384596012A", 11), 1009⟩, ⟨decodeRow 12 ("3845960127A", 11), 1010⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("8459601273A", 11), 1011⟩, ⟨decodeRow 12 ("4596012738A", 9), 1012⟩, ⟨decodeRow 12 ("A4596012783", 9), 1011⟩, ⟨decodeRow 12 ("3A459601287", 11), 1010⟩, ⟨decodeRow 12 ("A4596012837", 9), 1011⟩, ⟨decodeRow 12 ("7A459601238", 11), 1010⟩, ⟨decodeRow 12 ("A4596012378", 11), 1011⟩, ⟨decodeRow 12 ("459601237A8", 11), 1012⟩])
                (.leaf [⟨decodeRow 12 ("59601237A48", 11), 1013⟩, ⟨decodeRow 12 ("9601237A458", 11), 1014⟩, ⟨decodeRow 12 ("601237A4598", 11), 1015⟩, ⟨decodeRow 12 ("01237A45968", 9), 1016⟩, ⟨decodeRow 12 ("801237A4569", 11), 1015⟩, ⟨decodeRow 12 ("01237A45689", 11), 1016⟩, ⟨decodeRow 12 ("1237A456809", 11), 1017⟩, ⟨decodeRow 12 ("237A4568019", 11), 1018⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("37A45680129", 11), 1019⟩, ⟨decodeRow 12 ("7A456801239", 11), 1020⟩, ⟨decodeRow 12 ("A4568012379", 11), 1021⟩, ⟨decodeRow 12 ("456801237A9", 11), 1022⟩, ⟨decodeRow 12 ("56801237A49", 9), 1023⟩, ⟨decodeRow 12 ("9568012374A", 9), 1022⟩, ⟨decodeRow 12 ("A9568012347", 11), 1021⟩, ⟨decodeRow 12 ("956801234A7", 11), 1022⟩])
                (.leaf [⟨decodeRow 12 ("56801234A97", 11), 1023⟩, ⟨decodeRow 12 ("6801234A957", 11), 1024⟩, ⟨decodeRow 12 ("801234A9567", 11), 1025⟩, ⟨decodeRow 12 ("01234A95687", 11), 1026⟩, ⟨decodeRow 12 ("1234A956807", 9), 1027⟩, ⟨decodeRow 12 ("71234A95608", 11), 1026⟩, ⟨decodeRow 12 ("1234A956078", 11), 1027⟩, ⟨decodeRow 12 ("234A9560718", 9), 1028⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("8234A956017", 11), 1027⟩, ⟨decodeRow 12 ("234A9560187", 11), 1028⟩, ⟨decodeRow 12 ("34A95601827", 9), 1029⟩, ⟨decodeRow 12 ("734A9560128", 11), 1028⟩, ⟨decodeRow 12 ("34A95601278", 11), 1029⟩, ⟨decodeRow 12 ("4A956012738", 11), 1030⟩, ⟨decodeRow 12 ("A9560127348", 11), 1031⟩, ⟨decodeRow 12 ("956012734A8", 11), 1032⟩])
                (.leaf [⟨decodeRow 12 ("56012734A98", 11), 1033⟩, ⟨decodeRow 12 ("6012734A958", 9), 1034⟩, ⟨decodeRow 12 ("86012734A59", 11), 1033⟩, ⟨decodeRow 12 ("6012734A589", 11), 1034⟩, ⟨decodeRow 12 ("012734A5869", 11), 1035⟩, ⟨decodeRow 12 ("12734A58609", 11), 1036⟩, ⟨decodeRow 12 ("2734A586019", 11), 1037⟩, ⟨decodeRow 12 ("734A5860129", 11), 1038⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("34A58601279", 11), 1039⟩, ⟨decodeRow 12 ("4A586012739", 9), 1040⟩, ⟨decodeRow 12 ("94A58601237", 11), 1039⟩, ⟨decodeRow 12 ("4A586012397", 11), 1040⟩, ⟨decodeRow 12 ("A5860123947", 11), 1041⟩, ⟨decodeRow 12 ("586012394A7", 11), 1042⟩, ⟨decodeRow 12 ("86012394A57", 11), 1043⟩, ⟨decodeRow 12 ("6012394A587", 11), 1044⟩])
                (.leaf [⟨decodeRow 12 ("012394A5867", 9), 1045⟩, ⟨decodeRow 12 ("7012394A568", 11), 1044⟩, ⟨decodeRow 12 ("012394A5678", 11), 1045⟩, ⟨decodeRow 12 ("12394A56708", 9), 1046⟩, ⟨decodeRow 12 ("812394A5607", 11), 1045⟩, ⟨decodeRow 12 ("12394A56087", 11), 1046⟩, ⟨decodeRow 12 ("2394A560817", 9), 1047⟩, ⟨decodeRow 12 ("72394A56018", 11), 1046⟩])))))
        (.branch 63
          (.branch 31
            (.branch 15
              (.branch 7
                (.leaf [⟨decodeRow 12 ("2394A560178", 11), 1047⟩, ⟨decodeRow 12 ("394A5601728", 11), 1048⟩, ⟨decodeRow 12 ("94A56017238", 11), 1049⟩, ⟨decodeRow 12 ("4A560172398", 11), 1050⟩, ⟨decodeRow 12 ("A5601723948", 9), 1051⟩, ⟨decodeRow 12 ("8A560172349", 11), 1050⟩, ⟨decodeRow 12 ("A5601723489", 11), 1051⟩])
                (.leaf [⟨decodeRow 12 ("560172348A9", 11), 1052⟩, ⟨decodeRow 12 ("60172348A59", 11), 1053⟩, ⟨decodeRow 12 ("0172348A569", 11), 1054⟩, ⟨decodeRow 12 ("172348A5609", 11), 1055⟩, ⟨decodeRow 12 ("72348A56019", 11), 1056⟩, ⟨decodeRow 12 ("2348A560179", 11), 1057⟩, ⟨decodeRow 12 ("348A5601729", 9), 1058⟩, ⟨decodeRow 12 ("9348A560127", 11), 1057⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("348A5601297", 11), 1058⟩, ⟨decodeRow 12 ("48A56012937", 11), 1059⟩, ⟨decodeRow 12 ("8A560129347", 11), 1060⟩, ⟨decodeRow 12 ("A5601293487", 11), 1061⟩, ⟨decodeRow 12 ("560129348A7", 11), 1062⟩, ⟨decodeRow 12 ("60129348A57", 9), 1063⟩, ⟨decodeRow 12 ("7601293485A", 9), 1062⟩, ⟨decodeRow 12 ("A7601293458", 11), 1061⟩])
                (.leaf [⟨decodeRow 12 ("760129345A8", 11), 1062⟩, ⟨decodeRow 12 ("60129345A78", 11), 1063⟩, ⟨decodeRow 12 ("0129345A768", 9), 1064⟩, ⟨decodeRow 12 ("80129345A67", 11), 1063⟩, ⟨decodeRow 12 ("0129345A687", 9), 1064⟩, ⟨decodeRow 12 ("70129345A86", 9), 1063⟩, ⟨decodeRow 12 ("6701293458A", 11), 1062⟩, ⟨decodeRow 12 ("7012934586A", 11), 1063⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("0129345867A", 11), 1064⟩, ⟨decodeRow 12 ("1293458670A", 9), 1065⟩, ⟨decodeRow 12 ("A1293458607", 11), 1064⟩, ⟨decodeRow 12 ("129345860A7", 9), 1065⟩, ⟨decodeRow 12 ("712934586A0", 9), 1064⟩, ⟨decodeRow 12 ("071293458A6", 9), 1063⟩, ⟨decodeRow 12 ("607129345A8", 11), 1062⟩, ⟨decodeRow 12 ("07129345A68", 11), 1063⟩])
                (.leaf [⟨decodeRow 12 ("7129345A608", 11), 1064⟩, ⟨decodeRow 12 ("129345A6078", 11), 1065⟩, ⟨decodeRow 12 ("29345A60718", 11), 1066⟩, ⟨decodeRow 12 ("9345A607128", 11), 1067⟩, ⟨decodeRow 12 ("345A6071298", 11), 1068⟩, ⟨decodeRow 12 ("45A60712938", 9), 1069⟩, ⟨decodeRow 12 ("845A6071239", 11), 1068⟩, ⟨decodeRow 12 ("45A60712389", 11), 1069⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("5A607123849", 11), 1070⟩, ⟨decodeRow 12 ("A6071238459", 11), 1071⟩, ⟨decodeRow 12 ("607123845A9", 11), 1072⟩, ⟨decodeRow 12 ("07123845A69", 11), 1073⟩, ⟨decodeRow 12 ("7123845A609", 11), 1074⟩, ⟨decodeRow 12 ("123845A6079", 11), 1075⟩, ⟨decodeRow 12 ("23845A60719", 9), 1076⟩, ⟨decodeRow 12 ("923845A6017", 11), 1075⟩])
                (.leaf [⟨decodeRow 12 ("23845A60197", 11), 1076⟩, ⟨decodeRow 12 ("3845A601927", 11), 1077⟩, ⟨decodeRow 12 ("845A6019237", 11), 1078⟩, ⟨decodeRow 12 ("45A60192387", 11), 1079⟩, ⟨decodeRow 12 ("5A601923847", 9), 1080⟩, ⟨decodeRow 12 ("75A60192348", 11), 1079⟩, ⟨decodeRow 12 ("5A601923478", 11), 1080⟩, ⟨decodeRow 12 ("A6019234758", 9), 1081⟩]))))
          (.branch 32
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("8A601923457", 11), 1080⟩, ⟨decodeRow 12 ("A6019234587", 11), 1081⟩, ⟨decodeRow 12 ("601923458A7", 11), 1082⟩, ⟨decodeRow 12 ("01923458A67", 9), 1083⟩, ⟨decodeRow 12 ("7019234586A", 9), 1082⟩, ⟨decodeRow 12 ("A7019234568", 11), 1081⟩, ⟨decodeRow 12 ("701923456A8", 11), 1082⟩, ⟨decodeRow 12 ("01923456A78", 11), 1083⟩])
                (.leaf [⟨decodeRow 12 ("1923456A708", 11), 1084⟩, ⟨decodeRow 12 ("923456A7018", 11), 1085⟩, ⟨decodeRow 12 ("23456A70198", 11), 1086⟩, ⟨decodeRow 12 ("3456A701928", 9), 1087⟩, ⟨decodeRow 12 ("83456A70129", 11), 1086⟩, ⟨decodeRow 12 ("3456A701289", 11), 1087⟩, ⟨decodeRow 12 ("456A7012839", 11), 1088⟩, ⟨decodeRow 12 ("56A70128349", 11), 1089⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("6A701283459", 11), 1090⟩, ⟨decodeRow 12 ("A7012834569", 11), 1091⟩, ⟨decodeRow 12 ("701283456A9", 11), 1092⟩, ⟨decodeRow 12 ("01283456A79", 11), 1093⟩, ⟨decodeRow 12 ("1283456A709", 9), 1094⟩, ⟨decodeRow 12 ("91283456A07", 11), 1093⟩, ⟨decodeRow 12 ("1283456A097", 11), 1094⟩, ⟨decodeRow 12 ("283456A0917", 11), 1095⟩])
                (.leaf [⟨decodeRow 12 ("83456A09127", 11), 1096⟩, ⟨decodeRow 12 ("3456A091287", 11), 1097⟩, ⟨decodeRow 12 ("456A0912837", 9), 1098⟩, ⟨decodeRow 12 ("7456A091238", 11), 1097⟩, ⟨decodeRow 12 ("456A0912378", 11), 1098⟩, ⟨decodeRow 12 ("56A09123748", 9), 1099⟩, ⟨decodeRow 12 ("856A0912347", 11), 1098⟩, ⟨decodeRow 12 ("56A09123487", 11), 1099⟩])))
            (.branch 16
              (.branch 8
                (.leaf [⟨decodeRow 12 ("6A091234857", 9), 1100⟩, ⟨decodeRow 12 ("76A09123458", 11), 1099⟩, ⟨decodeRow 12 ("6A091234578", 11), 1100⟩, ⟨decodeRow 12 ("A0912345768", 11), 1101⟩, ⟨decodeRow 12 ("091234576A8", 11), 1102⟩, ⟨decodeRow 12 ("91234576A08", 11), 1103⟩, ⟨decodeRow 12 ("1234576A098", 11), 1104⟩, ⟨decodeRow 12 ("234576A0918", 9), 1105⟩])
                (.leaf [⟨decodeRow 12 ("8234576A019", 11), 1104⟩, ⟨decodeRow 12 ("234576A0189", 11), 1105⟩, ⟨decodeRow 12 ("34576A01829", 11), 1106⟩, ⟨decodeRow 12 ("4576A018239", 11), 1107⟩, ⟨decodeRow 12 ("576A0182349", 11), 1108⟩, ⟨decodeRow 12 ("76A01823459", 11), 1109⟩, ⟨decodeRow 12 ("6A018234579", 11), 1110⟩, ⟨decodeRow 12 ("A0182345769", 9), 1111⟩]))
              (.branch 8
                (.leaf [⟨decodeRow 12 ("9A018234567", 11), 1110⟩, ⟨decodeRow 12 ("A0182345697", 11), 1111⟩, ⟨decodeRow 12 ("018234569A7", 11), 1112⟩, ⟨decodeRow 12 ("18234569A07", 11), 1113⟩, ⟨decodeRow 12 ("8234569A017", 11), 1114⟩, ⟨decodeRow 12 ("234569A0187", 11), 1115⟩, ⟨decodeRow 12 ("34569A01827", 9), 1116⟩, ⟨decodeRow 12 ("734569A0128", 11), 1115⟩])
                (.leaf [⟨decodeRow 12 ("34569A01278", 11), 1116⟩, ⟨decodeRow 12 ("4569A012738", 9), 1117⟩, ⟨decodeRow 12 ("84569A01237", 11), 1116⟩, ⟨decodeRow 12 ("4569A012387", 11), 1117⟩, ⟨decodeRow 12 ("569A0123847", 9), 1118⟩, ⟨decodeRow 12 ("7569A012348", 11), 1117⟩, ⟨decodeRow 12 ("569A0123478", 11), 1118⟩, ⟨decodeRow 12 ("69A01234758", 11), 1119⟩]))))))))

theorem rows_eq : tree.flatten.map Point.row = BlockF2.rows := by rfl

theorem excesses_eq : tree.flatten.map Point.excess = BlockF2.prefixes := by rfl

noncomputable def point (i : Nat) : Option Point := tree.get? i

theorem point_sound (i : Nat) {p : Point} (hp : point i = some p) :
    p.Occurs BlockF2.rows :=
  PointTree.get_sound tree BlockF2.rows BlockF2.prefixes rows_eq excesses_eq
    BlockF2.prefixes_checked i hp

end SuperpermutationUpperBound.Native14.Pointers.FastBlockF2
