module

public import upper.pointers.PointTree
public import upper.certificate.BlockF1Prefixes

@[expose] public section

/-! Balanced source-point data. Both projections are kernel checked once;
lookup soundness then follows from literal membership in this tree. -/
namespace SuperpermutationUpperBound.Native14.Pointers.FastBlockF1
open Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

noncomputable def tree : PointTree :=
  .branch 665
  (.branch 332
    (.branch 166
      (.branch 83
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A0123458679", 11), 0⟩, ⟨decodeRow 12 ("012345867A9", 11), 1⟩, ⟨decodeRow 12 ("12345867A09", 9), 2⟩, ⟨decodeRow 12 ("9123458670A", 9), 1⟩, ⟨decodeRow 12 ("A9123458607", 11), 0⟩])
                (.leaf [⟨decodeRow 12 ("912345860A7", 11), 1⟩, ⟨decodeRow 12 ("12345860A97", 11), 2⟩, ⟨decodeRow 12 ("2345860A917", 9), 3⟩, ⟨decodeRow 12 ("72345860A19", 11), 2⟩, ⟨decodeRow 12 ("2345860A179", 11), 3⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("345860A1729", 11), 4⟩, ⟨decodeRow 12 ("45860A17239", 11), 5⟩, ⟨decodeRow 12 ("5860A172349", 11), 6⟩, ⟨decodeRow 12 ("860A1723459", 11), 7⟩, ⟨decodeRow 12 ("60A17234589", 11), 8⟩])
                (.leaf [⟨decodeRow 12 ("0A172345869", 9), 9⟩, ⟨decodeRow 12 ("90A17234568", 11), 8⟩, ⟨decodeRow 12 ("0A172345698", 11), 9⟩, ⟨decodeRow 12 ("A1723456908", 9), 10⟩, ⟨decodeRow 12 ("8A172345609", 11), 9⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A1723456089", 11), 10⟩, ⟨decodeRow 12 ("172345608A9", 11), 11⟩, ⟨decodeRow 12 ("72345608A19", 11), 12⟩, ⟨decodeRow 12 ("2345608A179", 11), 13⟩, ⟨decodeRow 12 ("345608A1729", 9), 14⟩])
                (.leaf [⟨decodeRow 12 ("9345608A127", 11), 13⟩, ⟨decodeRow 12 ("345608A1297", 11), 14⟩, ⟨decodeRow 12 ("45608A12937", 9), 15⟩, ⟨decodeRow 12 ("745608A1239", 11), 14⟩, ⟨decodeRow 12 ("45608A12379", 11), 15⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("5608A123749", 11), 16⟩, ⟨decodeRow 12 ("608A1237459", 11), 17⟩, ⟨decodeRow 12 ("08A12374569", 11), 18⟩, ⟨decodeRow 12 ("8A123745609", 11), 19⟩, ⟨decodeRow 12 ("A1237456089", 11), 20⟩])
                (.leaf [⟨decodeRow 12 ("123745608A9", 11), 21⟩, ⟨decodeRow 12 ("23745608A19", 9), 22⟩, ⟨decodeRow 12 ("9237456081A", 9), 21⟩, ⟨decodeRow 12 ("A9237456018", 11), 20⟩, ⟨decodeRow 12 ("923745601A8", 11), 21⟩, ⟨decodeRow 12 ("23745601A98", 11), 22⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("3745601A928", 9), 23⟩, ⟨decodeRow 12 ("83745601A29", 11), 22⟩, ⟨decodeRow 12 ("3745601A289", 11), 23⟩, ⟨decodeRow 12 ("745601A2839", 11), 24⟩, ⟨decodeRow 12 ("45601A28379", 11), 25⟩])
                (.leaf [⟨decodeRow 12 ("5601A283749", 9), 26⟩, ⟨decodeRow 12 ("95601A28347", 11), 25⟩, ⟨decodeRow 12 ("5601A283497", 11), 26⟩, ⟨decodeRow 12 ("601A2834957", 9), 27⟩, ⟨decodeRow 12 ("7601A283459", 11), 26⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("601A2834579", 11), 27⟩, ⟨decodeRow 12 ("01A28345769", 11), 28⟩, ⟨decodeRow 12 ("1A283457609", 11), 29⟩, ⟨decodeRow 12 ("A2834576019", 11), 30⟩, ⟨decodeRow 12 ("283457601A9", 11), 31⟩])
                (.leaf [⟨decodeRow 12 ("83457601A29", 11), 32⟩, ⟨decodeRow 12 ("3457601A289", 11), 33⟩, ⟨decodeRow 12 ("457601A2839", 9), 34⟩, ⟨decodeRow 12 ("9457601A238", 11), 33⟩, ⟨decodeRow 12 ("457601A2398", 11), 34⟩, ⟨decodeRow 12 ("57601A23948", 9), 35⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("857601A2349", 11), 34⟩, ⟨decodeRow 12 ("57601A23489", 11), 35⟩, ⟨decodeRow 12 ("7601A234859", 11), 36⟩, ⟨decodeRow 12 ("601A2348579", 11), 37⟩, ⟨decodeRow 12 ("01A23485769", 9), 38⟩])
                (.leaf [⟨decodeRow 12 ("901A2348567", 11), 37⟩, ⟨decodeRow 12 ("01A23485697", 11), 38⟩, ⟨decodeRow 12 ("1A234856907", 9), 39⟩, ⟨decodeRow 12 ("71A23485609", 11), 38⟩, ⟨decodeRow 12 ("1A234856079", 11), 39⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A2348560719", 11), 40⟩, ⟨decodeRow 12 ("234856071A9", 11), 41⟩, ⟨decodeRow 12 ("34856071A29", 11), 42⟩, ⟨decodeRow 12 ("4856071A239", 11), 43⟩, ⟨decodeRow 12 ("856071A2349", 11), 44⟩])
                (.leaf [⟨decodeRow 12 ("56071A23489", 11), 45⟩, ⟨decodeRow 12 ("6071A234859", 9), 46⟩, ⟨decodeRow 12 ("96071A23458", 11), 45⟩, ⟨decodeRow 12 ("6071A234598", 11), 46⟩, ⟨decodeRow 12 ("071A2345968", 9), 47⟩, ⟨decodeRow 12 ("8071A234569", 11), 46⟩])))))
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("071A2345689", 11), 47⟩, ⟨decodeRow 12 ("71A23456809", 11), 48⟩, ⟨decodeRow 12 ("1A234568079", 11), 49⟩, ⟨decodeRow 12 ("A2345680719", 9), 50⟩, ⟨decodeRow 12 ("9A234568017", 11), 49⟩])
                (.leaf [⟨decodeRow 12 ("A2345680197", 11), 50⟩, ⟨decodeRow 12 ("234568019A7", 11), 51⟩, ⟨decodeRow 12 ("34568019A27", 9), 52⟩, ⟨decodeRow 12 ("7345680192A", 9), 51⟩, ⟨decodeRow 12 ("A7345680129", 11), 50⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("734568012A9", 11), 51⟩, ⟨decodeRow 12 ("34568012A79", 11), 52⟩, ⟨decodeRow 12 ("4568012A739", 11), 53⟩, ⟨decodeRow 12 ("568012A7349", 11), 54⟩, ⟨decodeRow 12 ("68012A73459", 11), 55⟩])
                (.leaf [⟨decodeRow 12 ("8012A734569", 11), 56⟩, ⟨decodeRow 12 ("012A7345689", 11), 57⟩, ⟨decodeRow 12 ("12A73456809", 9), 58⟩, ⟨decodeRow 12 ("912A7345608", 11), 57⟩, ⟨decodeRow 12 ("12A73456098", 11), 58⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("2A734560918", 9), 59⟩, ⟨decodeRow 12 ("82A73456019", 11), 58⟩, ⟨decodeRow 12 ("2A734560189", 11), 59⟩, ⟨decodeRow 12 ("A7345601829", 11), 60⟩, ⟨decodeRow 12 ("734560182A9", 11), 61⟩])
                (.leaf [⟨decodeRow 12 ("34560182A79", 11), 62⟩, ⟨decodeRow 12 ("4560182A739", 9), 63⟩, ⟨decodeRow 12 ("94560182A37", 11), 62⟩, ⟨decodeRow 12 ("4560182A397", 11), 63⟩, ⟨decodeRow 12 ("560182A3947", 9), 64⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("7560182A349", 11), 63⟩, ⟨decodeRow 12 ("560182A3479", 11), 64⟩, ⟨decodeRow 12 ("60182A34759", 11), 65⟩, ⟨decodeRow 12 ("0182A347569", 11), 66⟩, ⟨decodeRow 12 ("182A3475609", 11), 67⟩])
                (.leaf [⟨decodeRow 12 ("82A34756019", 11), 68⟩, ⟨decodeRow 12 ("2A347560189", 11), 69⟩, ⟨decodeRow 12 ("A3475601829", 9), 70⟩, ⟨decodeRow 12 ("9A347560128", 11), 69⟩, ⟨decodeRow 12 ("A3475601298", 11), 70⟩, ⟨decodeRow 12 ("347560129A8", 11), 71⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("47560129A38", 9), 72⟩, ⟨decodeRow 12 ("8475601293A", 9), 71⟩, ⟨decodeRow 12 ("A8475601239", 11), 70⟩, ⟨decodeRow 12 ("847560123A9", 11), 71⟩, ⟨decodeRow 12 ("47560123A89", 11), 72⟩])
                (.leaf [⟨decodeRow 12 ("7560123A849", 11), 73⟩, ⟨decodeRow 12 ("560123A8479", 11), 74⟩, ⟨decodeRow 12 ("60123A84759", 9), 75⟩, ⟨decodeRow 12 ("960123A8457", 11), 74⟩, ⟨decodeRow 12 ("60123A84597", 11), 75⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("0123A845967", 9), 76⟩, ⟨decodeRow 12 ("70123A84569", 11), 75⟩, ⟨decodeRow 12 ("0123A845679", 11), 76⟩, ⟨decodeRow 12 ("123A8456709", 11), 77⟩, ⟨decodeRow 12 ("23A84567019", 11), 78⟩])
                (.leaf [⟨decodeRow 12 ("3A845670129", 11), 79⟩, ⟨decodeRow 12 ("A8456701239", 11), 80⟩, ⟨decodeRow 12 ("845670123A9", 11), 81⟩, ⟨decodeRow 12 ("45670123A89", 11), 82⟩, ⟨decodeRow 12 ("5670123A849", 9), 83⟩, ⟨decodeRow 12 ("95670123A48", 11), 82⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("5670123A498", 11), 83⟩, ⟨decodeRow 12 ("670123A4958", 9), 84⟩, ⟨decodeRow 12 ("8670123A459", 11), 83⟩, ⟨decodeRow 12 ("670123A4589", 11), 84⟩, ⟨decodeRow 12 ("70123A45869", 11), 85⟩])
                (.leaf [⟨decodeRow 12 ("0123A458679", 11), 86⟩, ⟨decodeRow 12 ("123A4586709", 9), 87⟩, ⟨decodeRow 12 ("9123A458607", 11), 86⟩, ⟨decodeRow 12 ("123A4586097", 11), 87⟩, ⟨decodeRow 12 ("23A45860917", 9), 88⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("723A4586019", 11), 87⟩, ⟨decodeRow 12 ("23A45860179", 11), 88⟩, ⟨decodeRow 12 ("3A458601729", 11), 89⟩, ⟨decodeRow 12 ("A4586017239", 11), 90⟩, ⟨decodeRow 12 ("458601723A9", 11), 91⟩])
                (.leaf [⟨decodeRow 12 ("58601723A49", 11), 92⟩, ⟨decodeRow 12 ("8601723A459", 11), 93⟩, ⟨decodeRow 12 ("601723A4589", 11), 94⟩, ⟨decodeRow 12 ("01723A45869", 9), 95⟩, ⟨decodeRow 12 ("901723A4568", 11), 94⟩, ⟨decodeRow 12 ("01723A45698", 11), 95⟩]))))))
      (.branch 83
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("1723A456908", 9), 96⟩, ⟨decodeRow 12 ("81723A45609", 11), 95⟩, ⟨decodeRow 12 ("1723A456089", 11), 96⟩, ⟨decodeRow 12 ("723A4560819", 11), 97⟩, ⟨decodeRow 12 ("23A45608179", 11), 98⟩])
                (.leaf [⟨decodeRow 12 ("3A456081729", 9), 99⟩, ⟨decodeRow 12 ("93A45608127", 11), 98⟩, ⟨decodeRow 12 ("3A456081297", 11), 99⟩, ⟨decodeRow 12 ("A4560812937", 9), 100⟩, ⟨decodeRow 12 ("7A456081239", 11), 99⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A4560812379", 11), 100⟩, ⟨decodeRow 12 ("456081237A9", 11), 101⟩, ⟨decodeRow 12 ("56081237A49", 11), 102⟩, ⟨decodeRow 12 ("6081237A459", 11), 103⟩, ⟨decodeRow 12 ("081237A4569", 11), 104⟩])
                (.leaf [⟨decodeRow 12 ("81237A45609", 11), 105⟩, ⟨decodeRow 12 ("1237A456089", 11), 106⟩, ⟨decodeRow 12 ("237A4560819", 9), 107⟩, ⟨decodeRow 12 ("9237A456018", 11), 106⟩, ⟨decodeRow 12 ("237A4560198", 11), 107⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("37A45601928", 9), 108⟩, ⟨decodeRow 12 ("837A4560129", 11), 107⟩, ⟨decodeRow 12 ("37A45601289", 11), 108⟩, ⟨decodeRow 12 ("7A456012839", 11), 109⟩, ⟨decodeRow 12 ("A4560128379", 11), 110⟩])
                (.leaf [⟨decodeRow 12 ("456012837A9", 11), 111⟩, ⟨decodeRow 12 ("56012837A49", 9), 112⟩, ⟨decodeRow 12 ("9560128374A", 9), 111⟩, ⟨decodeRow 12 ("A9560128347", 11), 110⟩, ⟨decodeRow 12 ("956012834A7", 11), 111⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("56012834A97", 11), 112⟩, ⟨decodeRow 12 ("6012834A957", 9), 113⟩, ⟨decodeRow 12 ("76012834A59", 11), 112⟩, ⟨decodeRow 12 ("6012834A579", 11), 113⟩, ⟨decodeRow 12 ("012834A5769", 11), 114⟩])
                (.leaf [⟨decodeRow 12 ("12834A57609", 11), 115⟩, ⟨decodeRow 12 ("2834A576019", 11), 116⟩, ⟨decodeRow 12 ("834A5760129", 11), 117⟩, ⟨decodeRow 12 ("34A57601289", 11), 118⟩, ⟨decodeRow 12 ("4A576012839", 9), 119⟩, ⟨decodeRow 12 ("94A57601238", 11), 118⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("4A576012398", 11), 119⟩, ⟨decodeRow 12 ("A5760123948", 9), 120⟩, ⟨decodeRow 12 ("8A576012349", 11), 119⟩, ⟨decodeRow 12 ("A5760123489", 11), 120⟩, ⟨decodeRow 12 ("576012348A9", 11), 121⟩])
                (.leaf [⟨decodeRow 12 ("76012348A59", 11), 122⟩, ⟨decodeRow 12 ("6012348A579", 11), 123⟩, ⟨decodeRow 12 ("012348A5769", 9), 124⟩, ⟨decodeRow 12 ("9012348A567", 11), 123⟩, ⟨decodeRow 12 ("012348A5697", 11), 124⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("12348A56907", 9), 125⟩, ⟨decodeRow 12 ("712348A5609", 11), 124⟩, ⟨decodeRow 12 ("12348A56079", 11), 125⟩, ⟨decodeRow 12 ("2348A560719", 11), 126⟩, ⟨decodeRow 12 ("348A5607129", 11), 127⟩])
                (.leaf [⟨decodeRow 12 ("48A56071239", 11), 128⟩, ⟨decodeRow 12 ("8A560712349", 11), 129⟩, ⟨decodeRow 12 ("A5607123489", 11), 130⟩, ⟨decodeRow 12 ("560712348A9", 11), 131⟩, ⟨decodeRow 12 ("60712348A59", 9), 132⟩, ⟨decodeRow 12 ("9607123485A", 9), 131⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A9607123458", 11), 130⟩, ⟨decodeRow 12 ("960712345A8", 11), 131⟩, ⟨decodeRow 12 ("60712345A98", 11), 132⟩, ⟨decodeRow 12 ("0712345A968", 9), 133⟩, ⟨decodeRow 12 ("80712345A69", 11), 132⟩])
                (.leaf [⟨decodeRow 12 ("0712345A689", 11), 133⟩, ⟨decodeRow 12 ("712345A6809", 11), 134⟩, ⟨decodeRow 12 ("12345A68079", 11), 135⟩, ⟨decodeRow 12 ("2345A680719", 9), 136⟩, ⟨decodeRow 12 ("92345A68017", 11), 135⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("2345A680197", 11), 136⟩, ⟨decodeRow 12 ("345A6801927", 9), 137⟩, ⟨decodeRow 12 ("7345A680129", 11), 136⟩, ⟨decodeRow 12 ("345A6801279", 11), 137⟩, ⟨decodeRow 12 ("45A68012739", 11), 138⟩])
                (.leaf [⟨decodeRow 12 ("5A680127349", 11), 139⟩, ⟨decodeRow 12 ("A6801273459", 11), 140⟩, ⟨decodeRow 12 ("680127345A9", 11), 141⟩, ⟨decodeRow 12 ("80127345A69", 11), 142⟩, ⟨decodeRow 12 ("0127345A689", 11), 143⟩, ⟨decodeRow 12 ("127345A6809", 9), 144⟩])))))
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("9127345A608", 11), 143⟩, ⟨decodeRow 12 ("127345A6098", 11), 144⟩, ⟨decodeRow 12 ("27345A60918", 9), 145⟩, ⟨decodeRow 12 ("827345A6019", 11), 144⟩, ⟨decodeRow 12 ("27345A60189", 11), 145⟩])
                (.leaf [⟨decodeRow 12 ("7345A601829", 11), 146⟩, ⟨decodeRow 12 ("345A6018279", 11), 147⟩, ⟨decodeRow 12 ("45A60182739", 9), 148⟩, ⟨decodeRow 12 ("945A6018237", 11), 147⟩, ⟨decodeRow 12 ("45A60182397", 11), 148⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("5A601823947", 9), 149⟩, ⟨decodeRow 12 ("75A60182349", 11), 148⟩, ⟨decodeRow 12 ("5A601823479", 11), 149⟩, ⟨decodeRow 12 ("A6018234759", 11), 150⟩, ⟨decodeRow 12 ("601823475A9", 11), 151⟩])
                (.leaf [⟨decodeRow 12 ("01823475A69", 11), 152⟩, ⟨decodeRow 12 ("1823475A609", 11), 153⟩, ⟨decodeRow 12 ("823475A6019", 11), 154⟩, ⟨decodeRow 12 ("23475A60189", 11), 155⟩, ⟨decodeRow 12 ("3475A601829", 9), 156⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("93475A60128", 11), 155⟩, ⟨decodeRow 12 ("3475A601298", 11), 156⟩, ⟨decodeRow 12 ("475A6012938", 9), 157⟩, ⟨decodeRow 12 ("8475A601239", 11), 156⟩, ⟨decodeRow 12 ("475A6012389", 11), 157⟩])
                (.leaf [⟨decodeRow 12 ("75A60123849", 11), 158⟩, ⟨decodeRow 12 ("5A601238479", 11), 159⟩, ⟨decodeRow 12 ("A6012384759", 9), 160⟩, ⟨decodeRow 12 ("9A601238457", 11), 159⟩, ⟨decodeRow 12 ("A6012384597", 11), 160⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("601238459A7", 11), 161⟩, ⟨decodeRow 12 ("01238459A67", 9), 162⟩, ⟨decodeRow 12 ("7012384596A", 9), 161⟩, ⟨decodeRow 12 ("A7012384569", 11), 160⟩, ⟨decodeRow 12 ("701238456A9", 11), 161⟩])
                (.leaf [⟨decodeRow 12 ("01238456A79", 11), 162⟩, ⟨decodeRow 12 ("1238456A709", 11), 163⟩, ⟨decodeRow 12 ("238456A7019", 11), 164⟩, ⟨decodeRow 12 ("38456A70129", 11), 165⟩, ⟨decodeRow 12 ("8456A701239", 11), 166⟩, ⟨decodeRow 12 ("456A7012389", 11), 167⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("56A70123849", 9), 168⟩, ⟨decodeRow 12 ("956A7012348", 11), 167⟩, ⟨decodeRow 12 ("56A70123498", 11), 168⟩, ⟨decodeRow 12 ("6A701234958", 9), 169⟩, ⟨decodeRow 12 ("86A70123459", 11), 168⟩])
                (.leaf [⟨decodeRow 12 ("6A701234589", 11), 169⟩, ⟨decodeRow 12 ("A7012345869", 11), 170⟩, ⟨decodeRow 12 ("701234586A9", 11), 171⟩, ⟨decodeRow 12 ("01234586A79", 11), 172⟩, ⟨decodeRow 12 ("1234586A709", 9), 173⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("91234586A07", 11), 172⟩, ⟨decodeRow 12 ("1234586A097", 11), 173⟩, ⟨decodeRow 12 ("234586A0917", 9), 174⟩, ⟨decodeRow 12 ("7234586A019", 11), 173⟩, ⟨decodeRow 12 ("234586A0179", 11), 174⟩])
                (.leaf [⟨decodeRow 12 ("34586A01729", 11), 175⟩, ⟨decodeRow 12 ("4586A017239", 11), 176⟩, ⟨decodeRow 12 ("586A0172349", 11), 177⟩, ⟨decodeRow 12 ("86A01723459", 11), 178⟩, ⟨decodeRow 12 ("6A017234589", 11), 179⟩, ⟨decodeRow 12 ("A0172345869", 9), 180⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("9A017234568", 11), 179⟩, ⟨decodeRow 12 ("A0172345698", 11), 180⟩, ⟨decodeRow 12 ("017234569A8", 11), 181⟩, ⟨decodeRow 12 ("17234569A08", 9), 182⟩, ⟨decodeRow 12 ("8172345690A", 9), 181⟩])
                (.leaf [⟨decodeRow 12 ("A8172345609", 11), 180⟩, ⟨decodeRow 12 ("817234560A9", 11), 181⟩, ⟨decodeRow 12 ("17234560A89", 11), 182⟩, ⟨decodeRow 12 ("7234560A819", 11), 183⟩, ⟨decodeRow 12 ("234560A8179", 11), 184⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("34560A81729", 9), 185⟩, ⟨decodeRow 12 ("934560A8127", 11), 184⟩, ⟨decodeRow 12 ("34560A81297", 11), 185⟩, ⟨decodeRow 12 ("4560A812937", 9), 186⟩, ⟨decodeRow 12 ("74560A81239", 11), 185⟩])
                (.leaf [⟨decodeRow 12 ("4560A812379", 11), 186⟩, ⟨decodeRow 12 ("560A8123749", 11), 187⟩, ⟨decodeRow 12 ("60A81237459", 11), 188⟩, ⟨decodeRow 12 ("0A812374569", 11), 189⟩, ⟨decodeRow 12 ("A8123745609", 11), 190⟩, ⟨decodeRow 12 ("812374560A9", 11), 191⟩])))))))
    (.branch 166
      (.branch 83
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("12374560A89", 11), 192⟩, ⟨decodeRow 12 ("2374560A819", 9), 193⟩, ⟨decodeRow 12 ("92374560A18", 11), 192⟩, ⟨decodeRow 12 ("2374560A198", 11), 193⟩, ⟨decodeRow 12 ("374560A1928", 9), 194⟩])
                (.leaf [⟨decodeRow 12 ("8374560A129", 11), 193⟩, ⟨decodeRow 12 ("374560A1289", 11), 194⟩, ⟨decodeRow 12 ("74560A12839", 11), 195⟩, ⟨decodeRow 12 ("4560A128379", 11), 196⟩, ⟨decodeRow 12 ("560A1283749", 9), 197⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("9560A128347", 11), 196⟩, ⟨decodeRow 12 ("560A1283497", 11), 197⟩, ⟨decodeRow 12 ("60A12834957", 9), 198⟩, ⟨decodeRow 12 ("760A1283459", 11), 197⟩, ⟨decodeRow 12 ("60A12834579", 11), 198⟩])
                (.leaf [⟨decodeRow 12 ("0A128345769", 11), 199⟩, ⟨decodeRow 12 ("A1283457609", 11), 200⟩, ⟨decodeRow 12 ("128345760A9", 11), 201⟩, ⟨decodeRow 12 ("28345760A19", 11), 202⟩, ⟨decodeRow 12 ("8345760A129", 11), 203⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("345760A1289", 11), 204⟩, ⟨decodeRow 12 ("45760A12839", 9), 205⟩, ⟨decodeRow 12 ("945760A1238", 11), 204⟩, ⟨decodeRow 12 ("45760A12398", 11), 205⟩, ⟨decodeRow 12 ("5760A123948", 9), 206⟩])
                (.leaf [⟨decodeRow 12 ("85760A12349", 11), 205⟩, ⟨decodeRow 12 ("5760A123489", 11), 206⟩, ⟨decodeRow 12 ("760A1234859", 11), 207⟩, ⟨decodeRow 12 ("60A12348579", 11), 208⟩, ⟨decodeRow 12 ("0A123485769", 9), 209⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("90A12348567", 11), 208⟩, ⟨decodeRow 12 ("0A123485697", 11), 209⟩, ⟨decodeRow 12 ("A1234856907", 9), 210⟩, ⟨decodeRow 12 ("7A123485609", 11), 209⟩, ⟨decodeRow 12 ("A1234856079", 11), 210⟩])
                (.leaf [⟨decodeRow 12 ("123485607A9", 11), 211⟩, ⟨decodeRow 12 ("23485607A19", 11), 212⟩, ⟨decodeRow 12 ("3485607A129", 11), 213⟩, ⟨decodeRow 12 ("485607A1239", 11), 214⟩, ⟨decodeRow 12 ("85607A12349", 11), 215⟩, ⟨decodeRow 12 ("5607A123489", 11), 216⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("607A1234859", 9), 217⟩, ⟨decodeRow 12 ("9607A123458", 11), 216⟩, ⟨decodeRow 12 ("607A1234598", 11), 217⟩, ⟨decodeRow 12 ("07A12345968", 9), 218⟩, ⟨decodeRow 12 ("807A1234569", 11), 217⟩])
                (.leaf [⟨decodeRow 12 ("07A12345689", 11), 218⟩, ⟨decodeRow 12 ("7A123456809", 11), 219⟩, ⟨decodeRow 12 ("A1234568079", 11), 220⟩, ⟨decodeRow 12 ("123456807A9", 11), 221⟩, ⟨decodeRow 12 ("23456807A19", 9), 222⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("9234568071A", 9), 221⟩, ⟨decodeRow 12 ("A9234568017", 11), 220⟩, ⟨decodeRow 12 ("923456801A7", 11), 221⟩, ⟨decodeRow 12 ("23456801A97", 11), 222⟩, ⟨decodeRow 12 ("3456801A927", 9), 223⟩])
                (.leaf [⟨decodeRow 12 ("73456801A29", 11), 222⟩, ⟨decodeRow 12 ("3456801A279", 11), 223⟩, ⟨decodeRow 12 ("456801A2739", 11), 224⟩, ⟨decodeRow 12 ("56801A27349", 11), 225⟩, ⟨decodeRow 12 ("6801A273459", 11), 226⟩, ⟨decodeRow 12 ("801A2734569", 11), 227⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("01A27345689", 11), 228⟩, ⟨decodeRow 12 ("1A273456809", 9), 229⟩, ⟨decodeRow 12 ("91A27345608", 11), 228⟩, ⟨decodeRow 12 ("1A273456098", 11), 229⟩, ⟨decodeRow 12 ("A2734560918", 9), 230⟩])
                (.leaf [⟨decodeRow 12 ("8A273456019", 11), 229⟩, ⟨decodeRow 12 ("A2734560189", 11), 230⟩, ⟨decodeRow 12 ("273456018A9", 11), 231⟩, ⟨decodeRow 12 ("73456018A29", 11), 232⟩, ⟨decodeRow 12 ("3456018A279", 11), 233⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("456018A2739", 9), 234⟩, ⟨decodeRow 12 ("9456018A237", 11), 233⟩, ⟨decodeRow 12 ("456018A2397", 11), 234⟩, ⟨decodeRow 12 ("56018A23947", 9), 235⟩, ⟨decodeRow 12 ("756018A2349", 11), 234⟩])
                (.leaf [⟨decodeRow 12 ("56018A23479", 11), 235⟩, ⟨decodeRow 12 ("6018A234759", 11), 236⟩, ⟨decodeRow 12 ("018A2347569", 11), 237⟩, ⟨decodeRow 12 ("18A23475609", 11), 238⟩, ⟨decodeRow 12 ("8A234756019", 11), 239⟩, ⟨decodeRow 12 ("A2347560189", 11), 240⟩])))))
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("234756018A9", 11), 241⟩, ⟨decodeRow 12 ("34756018A29", 9), 242⟩, ⟨decodeRow 12 ("9347560182A", 9), 241⟩, ⟨decodeRow 12 ("A9347560128", 11), 240⟩, ⟨decodeRow 12 ("934756012A8", 11), 241⟩])
                (.leaf [⟨decodeRow 12 ("34756012A98", 11), 242⟩, ⟨decodeRow 12 ("4756012A938", 9), 243⟩, ⟨decodeRow 12 ("84756012A39", 11), 242⟩, ⟨decodeRow 12 ("4756012A389", 11), 243⟩, ⟨decodeRow 12 ("756012A3849", 11), 244⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("56012A38479", 11), 245⟩, ⟨decodeRow 12 ("6012A384759", 9), 246⟩, ⟨decodeRow 12 ("96012A38457", 11), 245⟩, ⟨decodeRow 12 ("6012A384597", 11), 246⟩, ⟨decodeRow 12 ("012A3845967", 9), 247⟩])
                (.leaf [⟨decodeRow 12 ("7012A384569", 11), 246⟩, ⟨decodeRow 12 ("012A3845679", 11), 247⟩, ⟨decodeRow 12 ("12A38456709", 11), 248⟩, ⟨decodeRow 12 ("2A384567019", 11), 249⟩, ⟨decodeRow 12 ("A3845670129", 11), 250⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("384567012A9", 11), 251⟩, ⟨decodeRow 12 ("84567012A39", 11), 252⟩, ⟨decodeRow 12 ("4567012A389", 11), 253⟩, ⟨decodeRow 12 ("567012A3849", 9), 254⟩, ⟨decodeRow 12 ("9567012A348", 11), 253⟩])
                (.leaf [⟨decodeRow 12 ("567012A3498", 11), 254⟩, ⟨decodeRow 12 ("67012A34958", 9), 255⟩, ⟨decodeRow 12 ("867012A3459", 11), 254⟩, ⟨decodeRow 12 ("67012A34589", 11), 255⟩, ⟨decodeRow 12 ("7012A345869", 11), 256⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("012A3458679", 11), 257⟩, ⟨decodeRow 12 ("12A34586709", 9), 258⟩, ⟨decodeRow 12 ("912A3458607", 11), 257⟩, ⟨decodeRow 12 ("12A34586097", 11), 258⟩, ⟨decodeRow 12 ("2A345860917", 9), 259⟩])
                (.leaf [⟨decodeRow 12 ("72A34586019", 11), 258⟩, ⟨decodeRow 12 ("2A345860179", 11), 259⟩, ⟨decodeRow 12 ("A3458601729", 11), 260⟩, ⟨decodeRow 12 ("345860172A9", 11), 261⟩, ⟨decodeRow 12 ("45860172A39", 11), 262⟩, ⟨decodeRow 12 ("5860172A349", 11), 263⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("860172A3459", 11), 264⟩, ⟨decodeRow 12 ("60172A34589", 11), 265⟩, ⟨decodeRow 12 ("0172A345869", 9), 266⟩, ⟨decodeRow 12 ("90172A34568", 11), 265⟩, ⟨decodeRow 12 ("0172A345698", 11), 266⟩])
                (.leaf [⟨decodeRow 12 ("172A3456908", 9), 267⟩, ⟨decodeRow 12 ("8172A345609", 11), 266⟩, ⟨decodeRow 12 ("172A3456089", 11), 267⟩, ⟨decodeRow 12 ("72A34560819", 11), 268⟩, ⟨decodeRow 12 ("2A345608179", 11), 269⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A3456081729", 9), 270⟩, ⟨decodeRow 12 ("9A345608127", 11), 269⟩, ⟨decodeRow 12 ("A3456081297", 11), 270⟩, ⟨decodeRow 12 ("345608129A7", 11), 271⟩, ⟨decodeRow 12 ("45608129A37", 9), 272⟩])
                (.leaf [⟨decodeRow 12 ("7456081293A", 9), 271⟩, ⟨decodeRow 12 ("A7456081239", 11), 270⟩, ⟨decodeRow 12 ("745608123A9", 11), 271⟩, ⟨decodeRow 12 ("45608123A79", 11), 272⟩, ⟨decodeRow 12 ("5608123A749", 11), 273⟩, ⟨decodeRow 12 ("608123A7459", 11), 274⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("08123A74569", 11), 275⟩, ⟨decodeRow 12 ("8123A745609", 11), 276⟩, ⟨decodeRow 12 ("123A7456089", 11), 277⟩, ⟨decodeRow 12 ("23A74560819", 9), 278⟩, ⟨decodeRow 12 ("923A7456018", 11), 277⟩])
                (.leaf [⟨decodeRow 12 ("23A74560198", 11), 278⟩, ⟨decodeRow 12 ("3A745601928", 9), 279⟩, ⟨decodeRow 12 ("83A74560129", 11), 278⟩, ⟨decodeRow 12 ("3A745601289", 11), 279⟩, ⟨decodeRow 12 ("A7456012839", 11), 280⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("745601283A9", 11), 281⟩, ⟨decodeRow 12 ("45601283A79", 11), 282⟩, ⟨decodeRow 12 ("5601283A749", 9), 283⟩, ⟨decodeRow 12 ("95601283A47", 11), 282⟩, ⟨decodeRow 12 ("5601283A497", 11), 283⟩])
                (.leaf [⟨decodeRow 12 ("601283A4957", 9), 284⟩, ⟨decodeRow 12 ("7601283A459", 11), 283⟩, ⟨decodeRow 12 ("601283A4579", 11), 284⟩, ⟨decodeRow 12 ("01283A45769", 11), 285⟩, ⟨decodeRow 12 ("1283A457609", 11), 286⟩, ⟨decodeRow 12 ("283A4576019", 11), 287⟩]))))))
      (.branch 83
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("83A45760129", 11), 288⟩, ⟨decodeRow 12 ("3A457601289", 11), 289⟩, ⟨decodeRow 12 ("A4576012839", 9), 290⟩, ⟨decodeRow 12 ("9A457601238", 11), 289⟩, ⟨decodeRow 12 ("A4576012398", 11), 290⟩])
                (.leaf [⟨decodeRow 12 ("457601239A8", 11), 291⟩, ⟨decodeRow 12 ("57601239A48", 9), 292⟩, ⟨decodeRow 12 ("8576012394A", 9), 291⟩, ⟨decodeRow 12 ("A8576012349", 11), 290⟩, ⟨decodeRow 12 ("857601234A9", 11), 291⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("57601234A89", 11), 292⟩, ⟨decodeRow 12 ("7601234A859", 11), 293⟩, ⟨decodeRow 12 ("601234A8579", 11), 294⟩, ⟨decodeRow 12 ("01234A85769", 9), 295⟩, ⟨decodeRow 12 ("901234A8567", 11), 294⟩])
                (.leaf [⟨decodeRow 12 ("01234A85697", 11), 295⟩, ⟨decodeRow 12 ("1234A856907", 9), 296⟩, ⟨decodeRow 12 ("71234A85609", 11), 295⟩, ⟨decodeRow 12 ("1234A856079", 11), 296⟩, ⟨decodeRow 12 ("234A8560719", 11), 297⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("34A85607129", 11), 298⟩, ⟨decodeRow 12 ("4A856071239", 11), 299⟩, ⟨decodeRow 12 ("A8560712349", 11), 300⟩, ⟨decodeRow 12 ("856071234A9", 11), 301⟩, ⟨decodeRow 12 ("56071234A89", 11), 302⟩])
                (.leaf [⟨decodeRow 12 ("6071234A859", 9), 303⟩, ⟨decodeRow 12 ("96071234A58", 11), 302⟩, ⟨decodeRow 12 ("6071234A598", 11), 303⟩, ⟨decodeRow 12 ("071234A5968", 9), 304⟩, ⟨decodeRow 12 ("8071234A569", 11), 303⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("071234A5689", 11), 304⟩, ⟨decodeRow 12 ("71234A56809", 11), 305⟩, ⟨decodeRow 12 ("1234A568079", 11), 306⟩, ⟨decodeRow 12 ("234A5680719", 9), 307⟩, ⟨decodeRow 12 ("9234A568017", 11), 306⟩])
                (.leaf [⟨decodeRow 12 ("234A5680197", 11), 307⟩, ⟨decodeRow 12 ("34A56801927", 9), 308⟩, ⟨decodeRow 12 ("734A5680129", 11), 307⟩, ⟨decodeRow 12 ("34A56801279", 11), 308⟩, ⟨decodeRow 12 ("4A568012739", 11), 309⟩, ⟨decodeRow 12 ("A5680127349", 11), 310⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("568012734A9", 11), 311⟩, ⟨decodeRow 12 ("68012734A59", 11), 312⟩, ⟨decodeRow 12 ("8012734A569", 11), 313⟩, ⟨decodeRow 12 ("012734A5689", 11), 314⟩, ⟨decodeRow 12 ("12734A56809", 9), 315⟩])
                (.leaf [⟨decodeRow 12 ("912734A5608", 11), 314⟩, ⟨decodeRow 12 ("12734A56098", 11), 315⟩, ⟨decodeRow 12 ("2734A560918", 9), 316⟩, ⟨decodeRow 12 ("82734A56019", 11), 315⟩, ⟨decodeRow 12 ("2734A560189", 11), 316⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("734A5601829", 11), 317⟩, ⟨decodeRow 12 ("34A56018279", 11), 318⟩, ⟨decodeRow 12 ("4A560182739", 9), 319⟩, ⟨decodeRow 12 ("94A56018237", 11), 318⟩, ⟨decodeRow 12 ("4A560182397", 11), 319⟩])
                (.leaf [⟨decodeRow 12 ("A5601823947", 9), 320⟩, ⟨decodeRow 12 ("7A560182349", 11), 319⟩, ⟨decodeRow 12 ("A5601823479", 11), 320⟩, ⟨decodeRow 12 ("560182347A9", 11), 321⟩, ⟨decodeRow 12 ("60182347A59", 11), 322⟩, ⟨decodeRow 12 ("0182347A569", 11), 323⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("182347A5609", 11), 324⟩, ⟨decodeRow 12 ("82347A56019", 11), 325⟩, ⟨decodeRow 12 ("2347A560189", 11), 326⟩, ⟨decodeRow 12 ("347A5601829", 9), 327⟩, ⟨decodeRow 12 ("9347A560128", 11), 326⟩])
                (.leaf [⟨decodeRow 12 ("347A5601298", 11), 327⟩, ⟨decodeRow 12 ("47A56012938", 9), 328⟩, ⟨decodeRow 12 ("847A5601239", 11), 327⟩, ⟨decodeRow 12 ("47A56012389", 11), 328⟩, ⟨decodeRow 12 ("7A560123849", 11), 329⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A5601238479", 11), 330⟩, ⟨decodeRow 12 ("560123847A9", 11), 331⟩, ⟨decodeRow 12 ("60123847A59", 9), 332⟩, ⟨decodeRow 12 ("9601238475A", 9), 331⟩, ⟨decodeRow 12 ("A9601238457", 11), 330⟩])
                (.leaf [⟨decodeRow 12 ("960123845A7", 11), 331⟩, ⟨decodeRow 12 ("60123845A97", 11), 332⟩, ⟨decodeRow 12 ("0123845A967", 9), 333⟩, ⟨decodeRow 12 ("70123845A69", 11), 332⟩, ⟨decodeRow 12 ("0123845A679", 11), 333⟩, ⟨decodeRow 12 ("123845A6709", 11), 334⟩])))))
        (.branch 42
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("23845A67019", 11), 335⟩, ⟨decodeRow 12 ("3845A670129", 11), 336⟩, ⟨decodeRow 12 ("845A6701239", 11), 337⟩, ⟨decodeRow 12 ("45A67012389", 11), 338⟩, ⟨decodeRow 12 ("5A670123849", 9), 339⟩])
                (.leaf [⟨decodeRow 12 ("95A67012348", 11), 338⟩, ⟨decodeRow 12 ("5A670123498", 11), 339⟩, ⟨decodeRow 12 ("A6701234958", 9), 340⟩, ⟨decodeRow 12 ("8A670123459", 11), 339⟩, ⟨decodeRow 12 ("A6701234589", 11), 340⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("670123458A9", 11), 341⟩, ⟨decodeRow 12 ("70123458A69", 11), 342⟩, ⟨decodeRow 12 ("0123458A679", 11), 343⟩, ⟨decodeRow 12 ("123458A6709", 9), 344⟩, ⟨decodeRow 12 ("9123458A607", 11), 343⟩])
                (.leaf [⟨decodeRow 12 ("123458A6097", 11), 344⟩, ⟨decodeRow 12 ("23458A60917", 9), 345⟩, ⟨decodeRow 12 ("723458A6019", 11), 344⟩, ⟨decodeRow 12 ("23458A60179", 11), 345⟩, ⟨decodeRow 12 ("3458A601729", 11), 346⟩, ⟨decodeRow 12 ("458A6017239", 11), 347⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("58A60172349", 11), 348⟩, ⟨decodeRow 12 ("8A601723459", 11), 349⟩, ⟨decodeRow 12 ("A6017234589", 11), 350⟩, ⟨decodeRow 12 ("601723458A9", 11), 351⟩, ⟨decodeRow 12 ("01723458A69", 9), 352⟩])
                (.leaf [⟨decodeRow 12 ("9017234586A", 9), 351⟩, ⟨decodeRow 12 ("A9017234568", 11), 350⟩, ⟨decodeRow 12 ("901723456A8", 11), 351⟩, ⟨decodeRow 12 ("01723456A98", 11), 352⟩, ⟨decodeRow 12 ("1723456A908", 9), 353⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("81723456A09", 11), 352⟩, ⟨decodeRow 12 ("1723456A089", 11), 353⟩, ⟨decodeRow 12 ("723456A0819", 11), 354⟩, ⟨decodeRow 12 ("23456A08179", 11), 355⟩, ⟨decodeRow 12 ("3456A081729", 9), 356⟩])
                (.leaf [⟨decodeRow 12 ("93456A08127", 11), 355⟩, ⟨decodeRow 12 ("3456A081297", 11), 356⟩, ⟨decodeRow 12 ("456A0812937", 9), 357⟩, ⟨decodeRow 12 ("7456A081239", 11), 356⟩, ⟨decodeRow 12 ("456A0812379", 11), 357⟩, ⟨decodeRow 12 ("56A08123749", 11), 358⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("6A081237459", 11), 359⟩, ⟨decodeRow 12 ("A0812374569", 11), 360⟩, ⟨decodeRow 12 ("081237456A9", 11), 361⟩, ⟨decodeRow 12 ("81237456A09", 11), 362⟩, ⟨decodeRow 12 ("1237456A089", 11), 363⟩])
                (.leaf [⟨decodeRow 12 ("237456A0819", 9), 364⟩, ⟨decodeRow 12 ("9237456A018", 11), 363⟩, ⟨decodeRow 12 ("237456A0198", 11), 364⟩, ⟨decodeRow 12 ("37456A01928", 9), 365⟩, ⟨decodeRow 12 ("837456A0129", 11), 364⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("37456A01289", 11), 365⟩, ⟨decodeRow 12 ("7456A012839", 11), 366⟩, ⟨decodeRow 12 ("456A0128379", 11), 367⟩, ⟨decodeRow 12 ("56A01283749", 9), 368⟩, ⟨decodeRow 12 ("956A0128347", 11), 367⟩])
                (.leaf [⟨decodeRow 12 ("56A01283497", 11), 368⟩, ⟨decodeRow 12 ("6A012834957", 9), 369⟩, ⟨decodeRow 12 ("76A01283459", 11), 368⟩, ⟨decodeRow 12 ("6A012834579", 11), 369⟩, ⟨decodeRow 12 ("A0128345769", 11), 370⟩, ⟨decodeRow 12 ("012834576A9", 11), 371⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("12834576A09", 11), 372⟩, ⟨decodeRow 12 ("2834576A019", 11), 373⟩, ⟨decodeRow 12 ("834576A0129", 11), 374⟩, ⟨decodeRow 12 ("34576A01289", 11), 375⟩, ⟨decodeRow 12 ("4576A012839", 9), 376⟩])
                (.leaf [⟨decodeRow 12 ("94576A01238", 11), 375⟩, ⟨decodeRow 12 ("4576A012398", 11), 376⟩, ⟨decodeRow 12 ("576A0123948", 9), 377⟩, ⟨decodeRow 12 ("8576A012349", 11), 376⟩, ⟨decodeRow 12 ("576A0123489", 11), 377⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("76A01234859", 11), 378⟩, ⟨decodeRow 12 ("6A012348579", 11), 379⟩, ⟨decodeRow 12 ("A0123485769", 9), 380⟩, ⟨decodeRow 12 ("9A012348567", 11), 379⟩, ⟨decodeRow 12 ("A0123485697", 11), 380⟩])
                (.leaf [⟨decodeRow 12 ("012348569A7", 11), 381⟩, ⟨decodeRow 12 ("12348569A07", 9), 382⟩, ⟨decodeRow 12 ("7123485690A", 9), 381⟩, ⟨decodeRow 12 ("A7123485609", 11), 380⟩, ⟨decodeRow 12 ("712348560A9", 11), 381⟩, ⟨decodeRow 12 ("12348560A79", 11), 382⟩]))))))))
  (.branch 332
    (.branch 166
      (.branch 83
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("2348560A719", 11), 383⟩, ⟨decodeRow 12 ("348560A7129", 11), 384⟩, ⟨decodeRow 12 ("48560A71239", 11), 385⟩, ⟨decodeRow 12 ("8560A712349", 11), 386⟩, ⟨decodeRow 12 ("560A7123489", 11), 387⟩])
                (.leaf [⟨decodeRow 12 ("60A71234859", 9), 388⟩, ⟨decodeRow 12 ("960A7123458", 11), 387⟩, ⟨decodeRow 12 ("60A71234598", 11), 388⟩, ⟨decodeRow 12 ("0A712345968", 9), 389⟩, ⟨decodeRow 12 ("80A71234569", 11), 388⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("0A712345689", 11), 389⟩, ⟨decodeRow 12 ("A7123456809", 11), 390⟩, ⟨decodeRow 12 ("712345680A9", 11), 391⟩, ⟨decodeRow 12 ("12345680A79", 11), 392⟩, ⟨decodeRow 12 ("2345680A719", 9), 393⟩])
                (.leaf [⟨decodeRow 12 ("92345680A17", 11), 392⟩, ⟨decodeRow 12 ("2345680A197", 11), 393⟩, ⟨decodeRow 12 ("345680A1927", 9), 394⟩, ⟨decodeRow 12 ("7345680A129", 11), 393⟩, ⟨decodeRow 12 ("345680A1279", 11), 394⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("45680A12739", 11), 395⟩, ⟨decodeRow 12 ("5680A127349", 11), 396⟩, ⟨decodeRow 12 ("680A1273459", 11), 397⟩, ⟨decodeRow 12 ("80A12734569", 11), 398⟩, ⟨decodeRow 12 ("0A127345689", 11), 399⟩])
                (.leaf [⟨decodeRow 12 ("A1273456809", 9), 400⟩, ⟨decodeRow 12 ("9A127345608", 11), 399⟩, ⟨decodeRow 12 ("A1273456098", 11), 400⟩, ⟨decodeRow 12 ("127345609A8", 11), 401⟩, ⟨decodeRow 12 ("27345609A18", 9), 402⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("8273456091A", 9), 401⟩, ⟨decodeRow 12 ("A8273456019", 11), 400⟩, ⟨decodeRow 12 ("827345601A9", 11), 401⟩, ⟨decodeRow 12 ("27345601A89", 11), 402⟩, ⟨decodeRow 12 ("7345601A829", 11), 403⟩])
                (.leaf [⟨decodeRow 12 ("345601A8279", 11), 404⟩, ⟨decodeRow 12 ("45601A82739", 9), 405⟩, ⟨decodeRow 12 ("945601A8237", 11), 404⟩, ⟨decodeRow 12 ("45601A82397", 11), 405⟩, ⟨decodeRow 12 ("5601A823947", 9), 406⟩, ⟨decodeRow 12 ("75601A82349", 11), 405⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("5601A823479", 11), 406⟩, ⟨decodeRow 12 ("601A8234759", 11), 407⟩, ⟨decodeRow 12 ("01A82347569", 11), 408⟩, ⟨decodeRow 12 ("1A823475609", 11), 409⟩, ⟨decodeRow 12 ("A8234756019", 11), 410⟩])
                (.leaf [⟨decodeRow 12 ("823475601A9", 11), 411⟩, ⟨decodeRow 12 ("23475601A89", 11), 412⟩, ⟨decodeRow 12 ("3475601A829", 9), 413⟩, ⟨decodeRow 12 ("93475601A28", 11), 412⟩, ⟨decodeRow 12 ("3475601A298", 11), 413⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("475601A2938", 9), 414⟩, ⟨decodeRow 12 ("8475601A239", 11), 413⟩, ⟨decodeRow 12 ("475601A2389", 11), 414⟩, ⟨decodeRow 12 ("75601A23849", 11), 415⟩, ⟨decodeRow 12 ("5601A238479", 11), 416⟩])
                (.leaf [⟨decodeRow 12 ("601A2384759", 9), 417⟩, ⟨decodeRow 12 ("9601A238457", 11), 416⟩, ⟨decodeRow 12 ("601A2384597", 11), 417⟩, ⟨decodeRow 12 ("01A23845967", 9), 418⟩, ⟨decodeRow 12 ("701A2384569", 11), 417⟩, ⟨decodeRow 12 ("01A23845679", 11), 418⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("1A238456709", 11), 419⟩, ⟨decodeRow 12 ("A2384567019", 11), 420⟩, ⟨decodeRow 12 ("238456701A9", 11), 421⟩, ⟨decodeRow 12 ("38456701A29", 11), 422⟩, ⟨decodeRow 12 ("8456701A239", 11), 423⟩])
                (.leaf [⟨decodeRow 12 ("456701A2389", 11), 424⟩, ⟨decodeRow 12 ("56701A23849", 9), 425⟩, ⟨decodeRow 12 ("956701A2348", 11), 424⟩, ⟨decodeRow 12 ("56701A23498", 11), 425⟩, ⟨decodeRow 12 ("6701A234958", 9), 426⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("86701A23459", 11), 425⟩, ⟨decodeRow 12 ("6701A234589", 11), 426⟩, ⟨decodeRow 12 ("701A2345869", 11), 427⟩, ⟨decodeRow 12 ("01A23458679", 11), 428⟩, ⟨decodeRow 12 ("1A234586709", 9), 429⟩])
                (.leaf [⟨decodeRow 12 ("91A23458607", 11), 428⟩, ⟨decodeRow 12 ("1A234586097", 11), 429⟩, ⟨decodeRow 12 ("A2345860917", 9), 430⟩, ⟨decodeRow 12 ("7A234586019", 11), 429⟩, ⟨decodeRow 12 ("A2345860179", 11), 430⟩, ⟨decodeRow 12 ("234586017A9", 11), 431⟩])))))
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("34586017A29", 11), 432⟩, ⟨decodeRow 12 ("4586017A239", 11), 433⟩, ⟨decodeRow 12 ("586017A2349", 11), 434⟩, ⟨decodeRow 12 ("86017A23459", 11), 435⟩, ⟨decodeRow 12 ("6017A234589", 11), 436⟩])
                (.leaf [⟨decodeRow 12 ("017A2345869", 9), 437⟩, ⟨decodeRow 12 ("9017A234568", 11), 436⟩, ⟨decodeRow 12 ("017A2345698", 11), 437⟩, ⟨decodeRow 12 ("17A23456908", 9), 438⟩, ⟨decodeRow 12 ("817A2345609", 11), 437⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("17A23456089", 11), 438⟩, ⟨decodeRow 12 ("7A234560819", 11), 439⟩, ⟨decodeRow 12 ("A2345608179", 11), 440⟩, ⟨decodeRow 12 ("234560817A9", 11), 441⟩, ⟨decodeRow 12 ("34560817A29", 9), 442⟩])
                (.leaf [⟨decodeRow 12 ("9345608172A", 9), 441⟩, ⟨decodeRow 12 ("A9345608127", 11), 440⟩, ⟨decodeRow 12 ("934560812A7", 11), 441⟩, ⟨decodeRow 12 ("34560812A97", 11), 442⟩, ⟨decodeRow 12 ("4560812A937", 9), 443⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("74560812A39", 11), 442⟩, ⟨decodeRow 12 ("4560812A379", 11), 443⟩, ⟨decodeRow 12 ("560812A3749", 11), 444⟩, ⟨decodeRow 12 ("60812A37459", 11), 445⟩, ⟨decodeRow 12 ("0812A374569", 11), 446⟩])
                (.leaf [⟨decodeRow 12 ("812A3745609", 11), 447⟩, ⟨decodeRow 12 ("12A37456089", 11), 448⟩, ⟨decodeRow 12 ("2A374560819", 9), 449⟩, ⟨decodeRow 12 ("92A37456018", 11), 448⟩, ⟨decodeRow 12 ("2A374560198", 11), 449⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A3745601928", 9), 450⟩, ⟨decodeRow 12 ("8A374560129", 11), 449⟩, ⟨decodeRow 12 ("A3745601289", 11), 450⟩, ⟨decodeRow 12 ("374560128A9", 11), 451⟩, ⟨decodeRow 12 ("74560128A39", 11), 452⟩])
                (.leaf [⟨decodeRow 12 ("4560128A379", 11), 453⟩, ⟨decodeRow 12 ("560128A3749", 9), 454⟩, ⟨decodeRow 12 ("9560128A347", 11), 453⟩, ⟨decodeRow 12 ("560128A3497", 11), 454⟩, ⟨decodeRow 12 ("60128A34957", 9), 455⟩, ⟨decodeRow 12 ("760128A3459", 11), 454⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("60128A34579", 11), 455⟩, ⟨decodeRow 12 ("0128A345769", 11), 456⟩, ⟨decodeRow 12 ("128A3457609", 11), 457⟩, ⟨decodeRow 12 ("28A34576019", 11), 458⟩, ⟨decodeRow 12 ("8A345760129", 11), 459⟩])
                (.leaf [⟨decodeRow 12 ("A3457601289", 11), 460⟩, ⟨decodeRow 12 ("345760128A9", 11), 461⟩, ⟨decodeRow 12 ("45760128A39", 9), 462⟩, ⟨decodeRow 12 ("9457601283A", 9), 461⟩, ⟨decodeRow 12 ("A9457601238", 11), 460⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("945760123A8", 11), 461⟩, ⟨decodeRow 12 ("45760123A98", 11), 462⟩, ⟨decodeRow 12 ("5760123A948", 9), 463⟩, ⟨decodeRow 12 ("85760123A49", 11), 462⟩, ⟨decodeRow 12 ("5760123A489", 11), 463⟩])
                (.leaf [⟨decodeRow 12 ("760123A4859", 11), 464⟩, ⟨decodeRow 12 ("60123A48579", 11), 465⟩, ⟨decodeRow 12 ("0123A485769", 9), 466⟩, ⟨decodeRow 12 ("90123A48567", 11), 465⟩, ⟨decodeRow 12 ("0123A485697", 11), 466⟩, ⟨decodeRow 12 ("123A4856907", 9), 467⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("7123A485609", 11), 466⟩, ⟨decodeRow 12 ("123A4856079", 11), 467⟩, ⟨decodeRow 12 ("23A48560719", 11), 468⟩, ⟨decodeRow 12 ("3A485607129", 11), 469⟩, ⟨decodeRow 12 ("A4856071239", 11), 470⟩])
                (.leaf [⟨decodeRow 12 ("485607123A9", 11), 471⟩, ⟨decodeRow 12 ("85607123A49", 11), 472⟩, ⟨decodeRow 12 ("5607123A489", 11), 473⟩, ⟨decodeRow 12 ("607123A4859", 9), 474⟩, ⟨decodeRow 12 ("9607123A458", 11), 473⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("607123A4598", 11), 474⟩, ⟨decodeRow 12 ("07123A45968", 9), 475⟩, ⟨decodeRow 12 ("807123A4569", 11), 474⟩, ⟨decodeRow 12 ("07123A45689", 11), 475⟩, ⟨decodeRow 12 ("7123A456809", 11), 476⟩])
                (.leaf [⟨decodeRow 12 ("123A4568079", 11), 477⟩, ⟨decodeRow 12 ("23A45680719", 9), 478⟩, ⟨decodeRow 12 ("923A4568017", 11), 477⟩, ⟨decodeRow 12 ("23A45680197", 11), 478⟩, ⟨decodeRow 12 ("3A456801927", 9), 479⟩, ⟨decodeRow 12 ("73A45680129", 11), 478⟩]))))))
      (.branch 83
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("3A456801279", 11), 479⟩, ⟨decodeRow 12 ("A4568012739", 11), 480⟩, ⟨decodeRow 12 ("456801273A9", 11), 481⟩, ⟨decodeRow 12 ("56801273A49", 11), 482⟩, ⟨decodeRow 12 ("6801273A459", 11), 483⟩])
                (.leaf [⟨decodeRow 12 ("801273A4569", 11), 484⟩, ⟨decodeRow 12 ("01273A45689", 11), 485⟩, ⟨decodeRow 12 ("1273A456809", 9), 486⟩, ⟨decodeRow 12 ("91273A45608", 11), 485⟩, ⟨decodeRow 12 ("1273A456098", 11), 486⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("273A4560918", 9), 487⟩, ⟨decodeRow 12 ("8273A456019", 11), 486⟩, ⟨decodeRow 12 ("273A4560189", 11), 487⟩, ⟨decodeRow 12 ("73A45601829", 11), 488⟩, ⟨decodeRow 12 ("3A456018279", 11), 489⟩])
                (.leaf [⟨decodeRow 12 ("A4560182739", 9), 490⟩, ⟨decodeRow 12 ("9A456018237", 11), 489⟩, ⟨decodeRow 12 ("A4560182397", 11), 490⟩, ⟨decodeRow 12 ("456018239A7", 11), 491⟩, ⟨decodeRow 12 ("56018239A47", 9), 492⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("7560182394A", 9), 491⟩, ⟨decodeRow 12 ("A7560182349", 11), 490⟩, ⟨decodeRow 12 ("756018234A9", 11), 491⟩, ⟨decodeRow 12 ("56018234A79", 11), 492⟩, ⟨decodeRow 12 ("6018234A759", 11), 493⟩])
                (.leaf [⟨decodeRow 12 ("018234A7569", 11), 494⟩, ⟨decodeRow 12 ("18234A75609", 11), 495⟩, ⟨decodeRow 12 ("8234A756019", 11), 496⟩, ⟨decodeRow 12 ("234A7560189", 11), 497⟩, ⟨decodeRow 12 ("34A75601829", 9), 498⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("934A7560128", 11), 497⟩, ⟨decodeRow 12 ("34A75601298", 11), 498⟩, ⟨decodeRow 12 ("4A756012938", 9), 499⟩, ⟨decodeRow 12 ("84A75601239", 11), 498⟩, ⟨decodeRow 12 ("4A756012389", 11), 499⟩])
                (.leaf [⟨decodeRow 12 ("A7560123849", 11), 500⟩, ⟨decodeRow 12 ("756012384A9", 11), 501⟩, ⟨decodeRow 12 ("56012384A79", 11), 502⟩, ⟨decodeRow 12 ("6012384A759", 9), 503⟩, ⟨decodeRow 12 ("96012384A57", 11), 502⟩, ⟨decodeRow 12 ("6012384A597", 11), 503⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("012384A5967", 9), 504⟩, ⟨decodeRow 12 ("7012384A569", 11), 503⟩, ⟨decodeRow 12 ("012384A5679", 11), 504⟩, ⟨decodeRow 12 ("12384A56709", 11), 505⟩, ⟨decodeRow 12 ("2384A567019", 11), 506⟩])
                (.leaf [⟨decodeRow 12 ("384A5670129", 11), 507⟩, ⟨decodeRow 12 ("84A56701239", 11), 508⟩, ⟨decodeRow 12 ("4A567012389", 11), 509⟩, ⟨decodeRow 12 ("A5670123849", 9), 510⟩, ⟨decodeRow 12 ("9A567012348", 11), 509⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A5670123498", 11), 510⟩, ⟨decodeRow 12 ("567012349A8", 11), 511⟩, ⟨decodeRow 12 ("67012349A58", 9), 512⟩, ⟨decodeRow 12 ("8670123495A", 9), 511⟩, ⟨decodeRow 12 ("A8670123459", 11), 510⟩])
                (.leaf [⟨decodeRow 12 ("867012345A9", 11), 511⟩, ⟨decodeRow 12 ("67012345A89", 11), 512⟩, ⟨decodeRow 12 ("7012345A869", 11), 513⟩, ⟨decodeRow 12 ("012345A8679", 11), 514⟩, ⟨decodeRow 12 ("12345A86709", 9), 515⟩, ⟨decodeRow 12 ("912345A8607", 11), 514⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("12345A86097", 11), 515⟩, ⟨decodeRow 12 ("2345A860917", 9), 516⟩, ⟨decodeRow 12 ("72345A86019", 11), 515⟩, ⟨decodeRow 12 ("2345A860179", 11), 516⟩, ⟨decodeRow 12 ("345A8601729", 11), 517⟩])
                (.leaf [⟨decodeRow 12 ("45A86017239", 11), 518⟩, ⟨decodeRow 12 ("5A860172349", 11), 519⟩, ⟨decodeRow 12 ("A8601723459", 11), 520⟩, ⟨decodeRow 12 ("860172345A9", 11), 521⟩, ⟨decodeRow 12 ("60172345A89", 11), 522⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("0172345A869", 9), 523⟩, ⟨decodeRow 12 ("90172345A68", 11), 522⟩, ⟨decodeRow 12 ("0172345A698", 11), 523⟩, ⟨decodeRow 12 ("172345A6908", 9), 524⟩, ⟨decodeRow 12 ("8172345A609", 11), 523⟩])
                (.leaf [⟨decodeRow 12 ("172345A6089", 11), 524⟩, ⟨decodeRow 12 ("72345A60819", 11), 525⟩, ⟨decodeRow 12 ("2345A608179", 11), 526⟩, ⟨decodeRow 12 ("345A6081729", 9), 527⟩, ⟨decodeRow 12 ("9345A608127", 11), 526⟩, ⟨decodeRow 12 ("345A6081297", 11), 527⟩])))))
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("45A60812937", 9), 528⟩, ⟨decodeRow 12 ("745A6081239", 11), 527⟩, ⟨decodeRow 12 ("45A60812379", 11), 528⟩, ⟨decodeRow 12 ("5A608123749", 11), 529⟩, ⟨decodeRow 12 ("A6081237459", 11), 530⟩])
                (.leaf [⟨decodeRow 12 ("608123745A9", 11), 531⟩, ⟨decodeRow 12 ("08123745A69", 11), 532⟩, ⟨decodeRow 12 ("8123745A609", 11), 533⟩, ⟨decodeRow 12 ("123745A6089", 11), 534⟩, ⟨decodeRow 12 ("23745A60819", 9), 535⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("923745A6018", 11), 534⟩, ⟨decodeRow 12 ("23745A60198", 11), 535⟩, ⟨decodeRow 12 ("3745A601928", 9), 536⟩, ⟨decodeRow 12 ("83745A60129", 11), 535⟩, ⟨decodeRow 12 ("3745A601289", 11), 536⟩])
                (.leaf [⟨decodeRow 12 ("745A6012839", 11), 537⟩, ⟨decodeRow 12 ("45A60128379", 11), 538⟩, ⟨decodeRow 12 ("5A601283749", 9), 539⟩, ⟨decodeRow 12 ("95A60128347", 11), 538⟩, ⟨decodeRow 12 ("5A601283497", 11), 539⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A6012834957", 9), 540⟩, ⟨decodeRow 12 ("7A601283459", 11), 539⟩, ⟨decodeRow 12 ("A6012834579", 11), 540⟩, ⟨decodeRow 12 ("601283457A9", 11), 541⟩, ⟨decodeRow 12 ("01283457A69", 11), 542⟩])
                (.leaf [⟨decodeRow 12 ("1283457A609", 11), 543⟩, ⟨decodeRow 12 ("283457A6019", 11), 544⟩, ⟨decodeRow 12 ("83457A60129", 11), 545⟩, ⟨decodeRow 12 ("3457A601289", 11), 546⟩, ⟨decodeRow 12 ("457A6012839", 9), 547⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("9457A601238", 11), 546⟩, ⟨decodeRow 12 ("457A6012398", 11), 547⟩, ⟨decodeRow 12 ("57A60123948", 9), 548⟩, ⟨decodeRow 12 ("857A6012349", 11), 547⟩, ⟨decodeRow 12 ("57A60123489", 11), 548⟩])
                (.leaf [⟨decodeRow 12 ("7A601234859", 11), 549⟩, ⟨decodeRow 12 ("A6012348579", 11), 550⟩, ⟨decodeRow 12 ("601234857A9", 11), 551⟩, ⟨decodeRow 12 ("01234857A69", 9), 552⟩, ⟨decodeRow 12 ("9012348576A", 9), 551⟩, ⟨decodeRow 12 ("A9012348567", 11), 550⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("901234856A7", 11), 551⟩, ⟨decodeRow 12 ("01234856A97", 11), 552⟩, ⟨decodeRow 12 ("1234856A907", 9), 553⟩, ⟨decodeRow 12 ("71234856A09", 11), 552⟩, ⟨decodeRow 12 ("1234856A079", 11), 553⟩])
                (.leaf [⟨decodeRow 12 ("234856A0719", 11), 554⟩, ⟨decodeRow 12 ("34856A07129", 11), 555⟩, ⟨decodeRow 12 ("4856A071239", 11), 556⟩, ⟨decodeRow 12 ("856A0712349", 11), 557⟩, ⟨decodeRow 12 ("56A07123489", 11), 558⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("6A071234859", 9), 559⟩, ⟨decodeRow 12 ("96A07123458", 11), 558⟩, ⟨decodeRow 12 ("6A071234598", 11), 559⟩, ⟨decodeRow 12 ("A0712345968", 9), 560⟩, ⟨decodeRow 12 ("8A071234569", 11), 559⟩])
                (.leaf [⟨decodeRow 12 ("A0712345689", 11), 560⟩, ⟨decodeRow 12 ("071234568A9", 11), 561⟩, ⟨decodeRow 12 ("71234568A09", 11), 562⟩, ⟨decodeRow 12 ("1234568A079", 11), 563⟩, ⟨decodeRow 12 ("234568A0719", 9), 564⟩, ⟨decodeRow 12 ("9234568A017", 11), 563⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("234568A0197", 11), 564⟩, ⟨decodeRow 12 ("34568A01927", 9), 565⟩, ⟨decodeRow 12 ("734568A0129", 11), 564⟩, ⟨decodeRow 12 ("34568A01279", 11), 565⟩, ⟨decodeRow 12 ("4568A012739", 11), 566⟩])
                (.leaf [⟨decodeRow 12 ("568A0127349", 11), 567⟩, ⟨decodeRow 12 ("68A01273459", 11), 568⟩, ⟨decodeRow 12 ("8A012734569", 11), 569⟩, ⟨decodeRow 12 ("A0127345689", 11), 570⟩, ⟨decodeRow 12 ("012734568A9", 11), 571⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("12734568A09", 9), 572⟩, ⟨decodeRow 12 ("9127345680A", 9), 571⟩, ⟨decodeRow 12 ("A9127345608", 11), 570⟩, ⟨decodeRow 12 ("912734560A8", 11), 571⟩, ⟨decodeRow 12 ("12734560A98", 11), 572⟩])
                (.leaf [⟨decodeRow 12 ("2734560A918", 9), 573⟩, ⟨decodeRow 12 ("82734560A19", 11), 572⟩, ⟨decodeRow 12 ("2734560A189", 11), 573⟩, ⟨decodeRow 12 ("734560A1829", 11), 574⟩, ⟨decodeRow 12 ("34560A18279", 11), 575⟩, ⟨decodeRow 12 ("4560A182739", 9), 576⟩])))))))
    (.branch 166
      (.branch 83
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("94560A18237", 11), 575⟩, ⟨decodeRow 12 ("4560A182397", 11), 576⟩, ⟨decodeRow 12 ("560A1823947", 9), 577⟩, ⟨decodeRow 12 ("7560A182349", 11), 576⟩, ⟨decodeRow 12 ("560A1823479", 11), 577⟩])
                (.leaf [⟨decodeRow 12 ("60A18234759", 11), 578⟩, ⟨decodeRow 12 ("0A182347569", 11), 579⟩, ⟨decodeRow 12 ("A1823475609", 11), 580⟩, ⟨decodeRow 12 ("182347560A9", 11), 581⟩, ⟨decodeRow 12 ("82347560A19", 11), 582⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("2347560A189", 11), 583⟩, ⟨decodeRow 12 ("347560A1829", 9), 584⟩, ⟨decodeRow 12 ("9347560A128", 11), 583⟩, ⟨decodeRow 12 ("347560A1298", 11), 584⟩, ⟨decodeRow 12 ("47560A12938", 9), 585⟩])
                (.leaf [⟨decodeRow 12 ("847560A1239", 11), 584⟩, ⟨decodeRow 12 ("47560A12389", 11), 585⟩, ⟨decodeRow 12 ("7560A123849", 11), 586⟩, ⟨decodeRow 12 ("560A1238479", 11), 587⟩, ⟨decodeRow 12 ("60A12384759", 9), 588⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("960A1238457", 11), 587⟩, ⟨decodeRow 12 ("60A12384597", 11), 588⟩, ⟨decodeRow 12 ("0A123845967", 9), 589⟩, ⟨decodeRow 12 ("70A12384569", 11), 588⟩, ⟨decodeRow 12 ("0A123845679", 11), 589⟩])
                (.leaf [⟨decodeRow 12 ("A1238456709", 11), 590⟩, ⟨decodeRow 12 ("123845670A9", 11), 591⟩, ⟨decodeRow 12 ("23845670A19", 11), 592⟩, ⟨decodeRow 12 ("3845670A129", 11), 593⟩, ⟨decodeRow 12 ("845670A1239", 11), 594⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("45670A12389", 11), 595⟩, ⟨decodeRow 12 ("5670A123849", 9), 596⟩, ⟨decodeRow 12 ("95670A12348", 11), 595⟩, ⟨decodeRow 12 ("5670A123498", 11), 596⟩, ⟨decodeRow 12 ("670A1234958", 9), 597⟩])
                (.leaf [⟨decodeRow 12 ("8670A123459", 11), 596⟩, ⟨decodeRow 12 ("670A1234589", 11), 597⟩, ⟨decodeRow 12 ("70A12345869", 11), 598⟩, ⟨decodeRow 12 ("0A123458679", 11), 599⟩, ⟨decodeRow 12 ("A1234586709", 9), 600⟩, ⟨decodeRow 12 ("9A123458607", 11), 599⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A1234586097", 11), 600⟩, ⟨decodeRow 12 ("123458609A7", 11), 601⟩, ⟨decodeRow 12 ("23458609A17", 9), 602⟩, ⟨decodeRow 12 ("7234586091A", 9), 601⟩, ⟨decodeRow 12 ("A7234586019", 11), 600⟩])
                (.leaf [⟨decodeRow 12 ("723458601A9", 11), 601⟩, ⟨decodeRow 12 ("23458601A79", 11), 602⟩, ⟨decodeRow 12 ("3458601A729", 11), 603⟩, ⟨decodeRow 12 ("458601A7239", 11), 604⟩, ⟨decodeRow 12 ("58601A72349", 11), 605⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("8601A723459", 11), 606⟩, ⟨decodeRow 12 ("601A7234589", 11), 607⟩, ⟨decodeRow 12 ("01A72345869", 9), 608⟩, ⟨decodeRow 12 ("901A7234568", 11), 607⟩, ⟨decodeRow 12 ("01A72345698", 11), 608⟩])
                (.leaf [⟨decodeRow 12 ("1A723456908", 9), 609⟩, ⟨decodeRow 12 ("81A72345609", 11), 608⟩, ⟨decodeRow 12 ("1A723456089", 11), 609⟩, ⟨decodeRow 12 ("A7234560819", 11), 610⟩, ⟨decodeRow 12 ("723456081A9", 11), 611⟩, ⟨decodeRow 12 ("23456081A79", 11), 612⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("3456081A729", 9), 613⟩, ⟨decodeRow 12 ("93456081A27", 11), 612⟩, ⟨decodeRow 12 ("3456081A297", 11), 613⟩, ⟨decodeRow 12 ("456081A2937", 9), 614⟩, ⟨decodeRow 12 ("7456081A239", 11), 613⟩])
                (.leaf [⟨decodeRow 12 ("456081A2379", 11), 614⟩, ⟨decodeRow 12 ("56081A23749", 11), 615⟩, ⟨decodeRow 12 ("6081A237459", 11), 616⟩, ⟨decodeRow 12 ("081A2374569", 11), 617⟩, ⟨decodeRow 12 ("81A23745609", 11), 618⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("1A237456089", 11), 619⟩, ⟨decodeRow 12 ("A2374560819", 9), 620⟩, ⟨decodeRow 12 ("9A237456018", 11), 619⟩, ⟨decodeRow 12 ("A2374560198", 11), 620⟩, ⟨decodeRow 12 ("237456019A8", 11), 621⟩])
                (.leaf [⟨decodeRow 12 ("37456019A28", 9), 622⟩, ⟨decodeRow 12 ("8374560192A", 9), 621⟩, ⟨decodeRow 12 ("A8374560129", 11), 620⟩, ⟨decodeRow 12 ("837456012A9", 11), 621⟩, ⟨decodeRow 12 ("37456012A89", 11), 622⟩, ⟨decodeRow 12 ("7456012A839", 11), 623⟩])))))
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("456012A8379", 11), 624⟩, ⟨decodeRow 12 ("56012A83749", 9), 625⟩, ⟨decodeRow 12 ("956012A8347", 11), 624⟩, ⟨decodeRow 12 ("56012A83497", 11), 625⟩, ⟨decodeRow 12 ("6012A834957", 9), 626⟩])
                (.leaf [⟨decodeRow 12 ("76012A83459", 11), 625⟩, ⟨decodeRow 12 ("6012A834579", 11), 626⟩, ⟨decodeRow 12 ("012A8345769", 11), 627⟩, ⟨decodeRow 12 ("12A83457609", 11), 628⟩, ⟨decodeRow 12 ("2A834576019", 11), 629⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A8345760129", 11), 630⟩, ⟨decodeRow 12 ("834576012A9", 11), 631⟩, ⟨decodeRow 12 ("34576012A89", 11), 632⟩, ⟨decodeRow 12 ("4576012A839", 9), 633⟩, ⟨decodeRow 12 ("94576012A38", 11), 632⟩])
                (.leaf [⟨decodeRow 12 ("4576012A398", 11), 633⟩, ⟨decodeRow 12 ("576012A3948", 9), 634⟩, ⟨decodeRow 12 ("8576012A349", 11), 633⟩, ⟨decodeRow 12 ("576012A3489", 11), 634⟩, ⟨decodeRow 12 ("76012A34859", 11), 635⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("6012A348579", 11), 636⟩, ⟨decodeRow 12 ("012A3485769", 9), 637⟩, ⟨decodeRow 12 ("9012A348567", 11), 636⟩, ⟨decodeRow 12 ("012A3485697", 11), 637⟩, ⟨decodeRow 12 ("12A34856907", 9), 638⟩])
                (.leaf [⟨decodeRow 12 ("712A3485609", 11), 637⟩, ⟨decodeRow 12 ("12A34856079", 11), 638⟩, ⟨decodeRow 12 ("2A348560719", 11), 639⟩, ⟨decodeRow 12 ("A3485607129", 11), 640⟩, ⟨decodeRow 12 ("348560712A9", 11), 641⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("48560712A39", 11), 642⟩, ⟨decodeRow 12 ("8560712A349", 11), 643⟩, ⟨decodeRow 12 ("560712A3489", 11), 644⟩, ⟨decodeRow 12 ("60712A34859", 9), 645⟩, ⟨decodeRow 12 ("960712A3458", 11), 644⟩])
                (.leaf [⟨decodeRow 12 ("60712A34598", 11), 645⟩, ⟨decodeRow 12 ("0712A345968", 9), 646⟩, ⟨decodeRow 12 ("80712A34569", 11), 645⟩, ⟨decodeRow 12 ("0712A345689", 11), 646⟩, ⟨decodeRow 12 ("712A3456809", 11), 647⟩, ⟨decodeRow 12 ("12A34568079", 11), 648⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("2A345680719", 9), 649⟩, ⟨decodeRow 12 ("92A34568017", 11), 648⟩, ⟨decodeRow 12 ("2A345680197", 11), 649⟩, ⟨decodeRow 12 ("A3456801927", 9), 650⟩, ⟨decodeRow 12 ("7A345680129", 11), 649⟩])
                (.leaf [⟨decodeRow 12 ("A3456801279", 11), 650⟩, ⟨decodeRow 12 ("345680127A9", 11), 651⟩, ⟨decodeRow 12 ("45680127A39", 11), 652⟩, ⟨decodeRow 12 ("5680127A349", 11), 653⟩, ⟨decodeRow 12 ("680127A3459", 11), 654⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("80127A34569", 11), 655⟩, ⟨decodeRow 12 ("0127A345689", 11), 656⟩, ⟨decodeRow 12 ("127A3456809", 9), 657⟩, ⟨decodeRow 12 ("9127A345608", 11), 656⟩, ⟨decodeRow 12 ("127A3456098", 11), 657⟩])
                (.leaf [⟨decodeRow 12 ("27A34560918", 9), 658⟩, ⟨decodeRow 12 ("827A3456019", 11), 657⟩, ⟨decodeRow 12 ("27A34560189", 11), 658⟩, ⟨decodeRow 12 ("7A345601829", 11), 659⟩, ⟨decodeRow 12 ("A3456018279", 11), 660⟩, ⟨decodeRow 12 ("345601827A9", 11), 661⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("45601827A39", 9), 662⟩, ⟨decodeRow 12 ("9456018273A", 9), 661⟩, ⟨decodeRow 12 ("A9456018237", 11), 660⟩, ⟨decodeRow 12 ("945601823A7", 11), 661⟩, ⟨decodeRow 12 ("45601823A97", 11), 662⟩])
                (.leaf [⟨decodeRow 12 ("5601823A947", 9), 663⟩, ⟨decodeRow 12 ("75601823A49", 11), 662⟩, ⟨decodeRow 12 ("5601823A479", 11), 663⟩, ⟨decodeRow 12 ("601823A4759", 11), 664⟩, ⟨decodeRow 12 ("01823A47569", 11), 665⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("1823A475609", 11), 666⟩, ⟨decodeRow 12 ("823A4756019", 11), 667⟩, ⟨decodeRow 12 ("23A47560189", 11), 668⟩, ⟨decodeRow 12 ("3A475601829", 9), 669⟩, ⟨decodeRow 12 ("93A47560128", 11), 668⟩])
                (.leaf [⟨decodeRow 12 ("3A475601298", 11), 669⟩, ⟨decodeRow 12 ("A4756012938", 9), 670⟩, ⟨decodeRow 12 ("8A475601239", 11), 669⟩, ⟨decodeRow 12 ("A4756012389", 11), 670⟩, ⟨decodeRow 12 ("475601238A9", 11), 671⟩, ⟨decodeRow 12 ("75601238A49", 11), 672⟩]))))))
      (.branch 83
        (.branch 41
          (.branch 20
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("5601238A479", 11), 673⟩, ⟨decodeRow 12 ("601238A4759", 9), 674⟩, ⟨decodeRow 12 ("9601238A457", 11), 673⟩, ⟨decodeRow 12 ("601238A4597", 11), 674⟩, ⟨decodeRow 12 ("01238A45967", 9), 675⟩])
                (.leaf [⟨decodeRow 12 ("701238A4569", 11), 674⟩, ⟨decodeRow 12 ("01238A45679", 11), 675⟩, ⟨decodeRow 12 ("1238A456709", 11), 676⟩, ⟨decodeRow 12 ("238A4567019", 11), 677⟩, ⟨decodeRow 12 ("38A45670129", 11), 678⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("8A456701239", 11), 679⟩, ⟨decodeRow 12 ("A4567012389", 11), 680⟩, ⟨decodeRow 12 ("456701238A9", 11), 681⟩, ⟨decodeRow 12 ("56701238A49", 9), 682⟩, ⟨decodeRow 12 ("9567012384A", 9), 681⟩])
                (.leaf [⟨decodeRow 12 ("A9567012348", 11), 680⟩, ⟨decodeRow 12 ("956701234A8", 11), 681⟩, ⟨decodeRow 12 ("56701234A98", 11), 682⟩, ⟨decodeRow 12 ("6701234A958", 9), 683⟩, ⟨decodeRow 12 ("86701234A59", 11), 682⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("6701234A589", 11), 683⟩, ⟨decodeRow 12 ("701234A5869", 11), 684⟩, ⟨decodeRow 12 ("01234A58679", 11), 685⟩, ⟨decodeRow 12 ("1234A586709", 9), 686⟩, ⟨decodeRow 12 ("91234A58607", 11), 685⟩])
                (.leaf [⟨decodeRow 12 ("1234A586097", 11), 686⟩, ⟨decodeRow 12 ("234A5860917", 9), 687⟩, ⟨decodeRow 12 ("7234A586019", 11), 686⟩, ⟨decodeRow 12 ("234A5860179", 11), 687⟩, ⟨decodeRow 12 ("34A58601729", 11), 688⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("4A586017239", 11), 689⟩, ⟨decodeRow 12 ("A5860172349", 11), 690⟩, ⟨decodeRow 12 ("586017234A9", 11), 691⟩, ⟨decodeRow 12 ("86017234A59", 11), 692⟩, ⟨decodeRow 12 ("6017234A589", 11), 693⟩])
                (.leaf [⟨decodeRow 12 ("017234A5869", 9), 694⟩, ⟨decodeRow 12 ("9017234A568", 11), 693⟩, ⟨decodeRow 12 ("017234A5698", 11), 694⟩, ⟨decodeRow 12 ("17234A56908", 9), 695⟩, ⟨decodeRow 12 ("817234A5609", 11), 694⟩, ⟨decodeRow 12 ("17234A56089", 11), 695⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("7234A560819", 11), 696⟩, ⟨decodeRow 12 ("234A5608179", 11), 697⟩, ⟨decodeRow 12 ("34A56081729", 9), 698⟩, ⟨decodeRow 12 ("934A5608127", 11), 697⟩, ⟨decodeRow 12 ("34A56081297", 11), 698⟩])
                (.leaf [⟨decodeRow 12 ("4A560812937", 9), 699⟩, ⟨decodeRow 12 ("74A56081239", 11), 698⟩, ⟨decodeRow 12 ("4A560812379", 11), 699⟩, ⟨decodeRow 12 ("A5608123749", 11), 700⟩, ⟨decodeRow 12 ("560812374A9", 11), 701⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("60812374A59", 11), 702⟩, ⟨decodeRow 12 ("0812374A569", 11), 703⟩, ⟨decodeRow 12 ("812374A5609", 11), 704⟩, ⟨decodeRow 12 ("12374A56089", 11), 705⟩, ⟨decodeRow 12 ("2374A560819", 9), 706⟩])
                (.leaf [⟨decodeRow 12 ("92374A56018", 11), 705⟩, ⟨decodeRow 12 ("2374A560198", 11), 706⟩, ⟨decodeRow 12 ("374A5601928", 9), 707⟩, ⟨decodeRow 12 ("8374A560129", 11), 706⟩, ⟨decodeRow 12 ("374A5601289", 11), 707⟩, ⟨decodeRow 12 ("74A56012839", 11), 708⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("4A560128379", 11), 709⟩, ⟨decodeRow 12 ("A5601283749", 9), 710⟩, ⟨decodeRow 12 ("9A560128347", 11), 709⟩, ⟨decodeRow 12 ("A5601283497", 11), 710⟩, ⟨decodeRow 12 ("560128349A7", 11), 711⟩])
                (.leaf [⟨decodeRow 12 ("60128349A57", 9), 712⟩, ⟨decodeRow 12 ("7601283495A", 9), 711⟩, ⟨decodeRow 12 ("A7601283459", 11), 710⟩, ⟨decodeRow 12 ("760128345A9", 11), 711⟩, ⟨decodeRow 12 ("60128345A79", 11), 712⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("0128345A769", 11), 713⟩, ⟨decodeRow 12 ("128345A7609", 11), 714⟩, ⟨decodeRow 12 ("28345A76019", 11), 715⟩, ⟨decodeRow 12 ("8345A760129", 11), 716⟩, ⟨decodeRow 12 ("345A7601289", 11), 717⟩])
                (.leaf [⟨decodeRow 12 ("45A76012839", 9), 718⟩, ⟨decodeRow 12 ("945A7601238", 11), 717⟩, ⟨decodeRow 12 ("45A76012398", 11), 718⟩, ⟨decodeRow 12 ("5A760123948", 9), 719⟩, ⟨decodeRow 12 ("85A76012349", 11), 718⟩, ⟨decodeRow 12 ("5A760123489", 11), 719⟩])))))
        (.branch 42
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A7601234859", 11), 720⟩, ⟨decodeRow 12 ("760123485A9", 11), 721⟩, ⟨decodeRow 12 ("60123485A79", 11), 722⟩, ⟨decodeRow 12 ("0123485A769", 9), 723⟩, ⟨decodeRow 12 ("90123485A67", 11), 722⟩])
                (.leaf [⟨decodeRow 12 ("0123485A697", 11), 723⟩, ⟨decodeRow 12 ("123485A6907", 9), 724⟩, ⟨decodeRow 12 ("7123485A609", 11), 723⟩, ⟨decodeRow 12 ("123485A6079", 11), 724⟩, ⟨decodeRow 12 ("23485A60719", 11), 725⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("3485A607129", 11), 726⟩, ⟨decodeRow 12 ("485A6071239", 11), 727⟩, ⟨decodeRow 12 ("85A60712349", 11), 728⟩, ⟨decodeRow 12 ("5A607123489", 11), 729⟩, ⟨decodeRow 12 ("A6071234859", 9), 730⟩])
                (.leaf [⟨decodeRow 12 ("9A607123458", 11), 729⟩, ⟨decodeRow 12 ("A6071234598", 11), 730⟩, ⟨decodeRow 12 ("607123459A8", 11), 731⟩, ⟨decodeRow 12 ("07123459A68", 9), 732⟩, ⟨decodeRow 12 ("8071234596A", 9), 731⟩, ⟨decodeRow 12 ("A8071234569", 11), 730⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("807123456A9", 11), 731⟩, ⟨decodeRow 12 ("07123456A89", 11), 732⟩, ⟨decodeRow 12 ("7123456A809", 11), 733⟩, ⟨decodeRow 12 ("123456A8079", 11), 734⟩, ⟨decodeRow 12 ("23456A80719", 9), 735⟩])
                (.leaf [⟨decodeRow 12 ("923456A8017", 11), 734⟩, ⟨decodeRow 12 ("23456A80197", 11), 735⟩, ⟨decodeRow 12 ("3456A801927", 9), 736⟩, ⟨decodeRow 12 ("73456A80129", 11), 735⟩, ⟨decodeRow 12 ("3456A801279", 11), 736⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("456A8012739", 11), 737⟩, ⟨decodeRow 12 ("56A80127349", 11), 738⟩, ⟨decodeRow 12 ("6A801273459", 11), 739⟩, ⟨decodeRow 12 ("A8012734569", 11), 740⟩, ⟨decodeRow 12 ("801273456A9", 11), 741⟩])
                (.leaf [⟨decodeRow 12 ("01273456A89", 11), 742⟩, ⟨decodeRow 12 ("1273456A809", 9), 743⟩, ⟨decodeRow 12 ("91273456A08", 11), 742⟩, ⟨decodeRow 12 ("1273456A098", 11), 743⟩, ⟨decodeRow 12 ("273456A0918", 9), 744⟩, ⟨decodeRow 12 ("8273456A019", 11), 743⟩]))))
          (.branch 21
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("273456A0189", 11), 744⟩, ⟨decodeRow 12 ("73456A01829", 11), 745⟩, ⟨decodeRow 12 ("3456A018279", 11), 746⟩, ⟨decodeRow 12 ("456A0182739", 9), 747⟩, ⟨decodeRow 12 ("9456A018237", 11), 746⟩])
                (.leaf [⟨decodeRow 12 ("456A0182397", 11), 747⟩, ⟨decodeRow 12 ("56A01823947", 9), 748⟩, ⟨decodeRow 12 ("756A0182349", 11), 747⟩, ⟨decodeRow 12 ("56A01823479", 11), 748⟩, ⟨decodeRow 12 ("6A018234759", 11), 749⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("A0182347569", 11), 750⟩, ⟨decodeRow 12 ("018234756A9", 11), 751⟩, ⟨decodeRow 12 ("18234756A09", 11), 752⟩, ⟨decodeRow 12 ("8234756A019", 11), 753⟩, ⟨decodeRow 12 ("234756A0189", 11), 754⟩])
                (.leaf [⟨decodeRow 12 ("34756A01829", 9), 755⟩, ⟨decodeRow 12 ("934756A0128", 11), 754⟩, ⟨decodeRow 12 ("34756A01298", 11), 755⟩, ⟨decodeRow 12 ("4756A012938", 9), 756⟩, ⟨decodeRow 12 ("84756A01239", 11), 755⟩, ⟨decodeRow 12 ("4756A012389", 11), 756⟩])))
            (.branch 10
              (.branch 5
                (.leaf [⟨decodeRow 12 ("756A0123849", 11), 757⟩, ⟨decodeRow 12 ("56A01238479", 11), 758⟩, ⟨decodeRow 12 ("6A012384759", 9), 759⟩, ⟨decodeRow 12 ("96A01238457", 11), 758⟩, ⟨decodeRow 12 ("6A012384597", 11), 759⟩])
                (.leaf [⟨decodeRow 12 ("A0123845967", 9), 760⟩, ⟨decodeRow 12 ("7A012384569", 11), 759⟩, ⟨decodeRow 12 ("A0123845679", 11), 760⟩, ⟨decodeRow 12 ("012384567A9", 11), 761⟩, ⟨decodeRow 12 ("12384567A09", 11), 762⟩]))
              (.branch 5
                (.leaf [⟨decodeRow 12 ("2384567A019", 11), 763⟩, ⟨decodeRow 12 ("384567A0129", 11), 764⟩, ⟨decodeRow 12 ("84567A01239", 11), 765⟩, ⟨decodeRow 12 ("4567A012389", 11), 766⟩, ⟨decodeRow 12 ("567A0123849", 9), 767⟩])
                (.leaf [⟨decodeRow 12 ("9567A012348", 11), 766⟩, ⟨decodeRow 12 ("567A0123498", 11), 767⟩, ⟨decodeRow 12 ("67A01234958", 9), 768⟩, ⟨decodeRow 12 ("867A0123459", 11), 767⟩, ⟨decodeRow 12 ("67A01234589", 11), 768⟩, ⟨decodeRow 12 ("7A012345869", 11), 769⟩]))))))))

theorem rows_eq : tree.flatten.map Point.row = BlockF1.rows := by rfl

theorem excesses_eq : tree.flatten.map Point.excess = BlockF1.prefixes := by rfl

noncomputable def point (i : Nat) : Option Point := tree.get? i

theorem point_sound (i : Nat) {p : Point} (hp : point i = some p) :
    p.Occurs BlockF1.rows :=
  PointTree.get_sound tree BlockF1.rows BlockF1.prefixes rows_eq excesses_eq
    BlockF1.prefixes_checked i hp

end SuperpermutationUpperBound.Native14.Pointers.FastBlockF1
