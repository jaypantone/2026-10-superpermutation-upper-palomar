module

public import upper.pointers.PointTree
public import upper.certificate.Halfar1Prefixes

@[expose] public section

/-! Balanced source-point data. Both projections are kernel checked once;
lookup soundness then follows from literal membership in this tree. -/
namespace SuperpermutationUpperBound.Native14.Pointers.FastHalfar1
open Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

noncomputable def tree : PointTree :=
  .branch 1212
  (.branch 606
    (.branch 303
      (.branch 151
        (.branch 75
          (.branch 37
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("60123457", 6), 0⟩, ⟨decodeRow 12 ("76012354", 8), -1⟩, ⟨decodeRow 12 ("60123574", 8), 0⟩, ⟨decodeRow 12 ("01235764", 8), 1⟩])
                  (.leaf [⟨decodeRow 12 ("12357604", 6), 2⟩, ⟨decodeRow 12 ("41235706", 8), 1⟩, ⟨decodeRow 12 ("12357046", 8), 2⟩, ⟨decodeRow 12 ("23570416", 8), 3⟩, ⟨decodeRow 12 ("35704126", 6), 4⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("63570421", 8), 3⟩, ⟨decodeRow 12 ("35704261", 8), 4⟩, ⟨decodeRow 12 ("57042631", 8), 5⟩, ⟨decodeRow 12 ("70426351", 8), 6⟩])
                  (.leaf [⟨decodeRow 12 ("04263571", 8), 7⟩, ⟨decodeRow 12 ("42635701", 6), 8⟩, ⟨decodeRow 12 ("14263507", 6), 7⟩, ⟨decodeRow 12 ("71426305", 8), 6⟩, ⟨decodeRow 12 ("14263075", 8), 7⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("42630715", 8), 8⟩, ⟨decodeRow 12 ("26307145", 8), 9⟩, ⟨decodeRow 12 ("63071425", 6), 10⟩, ⟨decodeRow 12 ("56307124", 8), 9⟩])
                  (.leaf [⟨decodeRow 12 ("63071254", 8), 10⟩, ⟨decodeRow 12 ("30712564", 8), 11⟩, ⟨decodeRow 12 ("07125634", 6), 12⟩, ⟨decodeRow 12 ("40712536", 8), 11⟩, ⟨decodeRow 12 ("07125346", 8), 12⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("71253406", 8), 13⟩, ⟨decodeRow 12 ("12534076", 8), 14⟩, ⟨decodeRow 12 ("25340716", 6), 15⟩, ⟨decodeRow 12 ("62534017", 6), 14⟩, ⟨decodeRow 12 ("76253410", 8), 13⟩])
                  (.leaf [⟨decodeRow 12 ("62534170", 8), 14⟩, ⟨decodeRow 12 ("25341760", 8), 15⟩, ⟨decodeRow 12 ("53417620", 8), 16⟩, ⟨decodeRow 12 ("34176250", 6), 17⟩, ⟨decodeRow 12 ("03417652", 8), 16⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("34176502", 8), 17⟩, ⟨decodeRow 12 ("41765032", 8), 18⟩, ⟨decodeRow 12 ("17650342", 6), 19⟩, ⟨decodeRow 12 ("21765043", 8), 18⟩])
                  (.leaf [⟨decodeRow 12 ("17650423", 8), 19⟩, ⟨decodeRow 12 ("76504213", 6), 20⟩, ⟨decodeRow 12 ("37650412", 8), 19⟩, ⟨decodeRow 12 ("76504132", 8), 20⟩, ⟨decodeRow 12 ("65041372", 8), 21⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("50413762", 8), 22⟩, ⟨decodeRow 12 ("04137652", 6), 23⟩, ⟨decodeRow 12 ("20413756", 8), 22⟩, ⟨decodeRow 12 ("04137526", 8), 23⟩, ⟨decodeRow 12 ("41375206", 8), 24⟩])
                  (.leaf [⟨decodeRow 12 ("13752046", 8), 25⟩, ⟨decodeRow 12 ("37520416", 6), 26⟩, ⟨decodeRow 12 ("63752014", 8), 25⟩, ⟨decodeRow 12 ("37520164", 8), 26⟩, ⟨decodeRow 12 ("75201634", 8), 27⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("52016374", 8), 28⟩, ⟨decodeRow 12 ("20163754", 6), 29⟩, ⟨decodeRow 12 ("42016357", 6), 28⟩, ⟨decodeRow 12 ("74201653", 8), 27⟩])
                  (.leaf [⟨decodeRow 12 ("42016573", 8), 28⟩, ⟨decodeRow 12 ("20165743", 8), 29⟩, ⟨decodeRow 12 ("01657423", 8), 30⟩, ⟨decodeRow 12 ("16574203", 6), 31⟩, ⟨decodeRow 12 ("31657402", 8), 30⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("16574032", 8), 31⟩, ⟨decodeRow 12 ("65740312", 8), 32⟩, ⟨decodeRow 12 ("57403162", 6), 33⟩, ⟨decodeRow 12 ("25740361", 8), 32⟩, ⟨decodeRow 12 ("57403621", 8), 33⟩])
                  (.leaf [⟨decodeRow 12 ("74036251", 6), 34⟩, ⟨decodeRow 12 ("17403652", 8), 33⟩, ⟨decodeRow 12 ("74036512", 8), 34⟩, ⟨decodeRow 12 ("40365172", 8), 35⟩, ⟨decodeRow 12 ("03651742", 8), 36⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("36517402", 8), 37⟩, ⟨decodeRow 12 ("65174032", 6), 38⟩, ⟨decodeRow 12 ("26517430", 8), 37⟩, ⟨decodeRow 12 ("65174320", 8), 38⟩])
                  (.leaf [⟨decodeRow 12 ("51743260", 8), 39⟩, ⟨decodeRow 12 ("17432650", 6), 40⟩, ⟨decodeRow 12 ("01743256", 8), 39⟩, ⟨decodeRow 12 ("17432506", 8), 40⟩, ⟨decodeRow 12 ("74325016", 8), 41⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("43250176", 8), 42⟩, ⟨decodeRow 12 ("32501746", 6), 43⟩, ⟨decodeRow 12 ("63250147", 6), 42⟩, ⟨decodeRow 12 ("76325041", 8), 41⟩, ⟨decodeRow 12 ("63250471", 8), 42⟩])
                  (.leaf [⟨decodeRow 12 ("32504761", 8), 43⟩, ⟨decodeRow 12 ("25047631", 8), 44⟩, ⟨decodeRow 12 ("50476321", 6), 45⟩, ⟨decodeRow 12 ("15047623", 8), 44⟩, ⟨decodeRow 12 ("50476213", 8), 45⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("04762153", 8), 46⟩, ⟨decodeRow 12 ("47621503", 6), 47⟩, ⟨decodeRow 12 ("34762105", 8), 46⟩, ⟨decodeRow 12 ("47621035", 8), 47⟩])
                  (.leaf [⟨decodeRow 12 ("76210345", 6), 48⟩, ⟨decodeRow 12 ("57621043", 8), 47⟩, ⟨decodeRow 12 ("76210453", 8), 48⟩, ⟨decodeRow 12 ("62104573", 8), 49⟩, ⟨decodeRow 12 ("21045763", 8), 50⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("10457623", 6), 51⟩, ⟨decodeRow 12 ("31045726", 8), 50⟩, ⟨decodeRow 12 ("10457236", 8), 51⟩, ⟨decodeRow 12 ("04572316", 8), 52⟩, ⟨decodeRow 12 ("45723106", 8), 53⟩])
                  (.leaf [⟨decodeRow 12 ("57231046", 6), 54⟩, ⟨decodeRow 12 ("65723140", 8), 53⟩, ⟨decodeRow 12 ("57231460", 8), 54⟩, ⟨decodeRow 12 ("72314650", 8), 55⟩, ⟨decodeRow 12 ("23146570", 8), 56⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("31465720", 6), 57⟩, ⟨decodeRow 12 ("03146527", 6), 56⟩, ⟨decodeRow 12 ("70314625", 8), 55⟩, ⟨decodeRow 12 ("03146275", 8), 56⟩])
                  (.leaf [⟨decodeRow 12 ("31462705", 8), 57⟩, ⟨decodeRow 12 ("14627035", 8), 58⟩, ⟨decodeRow 12 ("46270315", 6), 59⟩, ⟨decodeRow 12 ("54627013", 8), 58⟩, ⟨decodeRow 12 ("46270153", 8), 59⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("62701543", 8), 60⟩, ⟨decodeRow 12 ("27015463", 6), 61⟩, ⟨decodeRow 12 ("32701564", 8), 60⟩, ⟨decodeRow 12 ("27015634", 8), 61⟩, ⟨decodeRow 12 ("70156324", 6), 62⟩])
                  (.leaf [⟨decodeRow 12 ("47015623", 8), 61⟩, ⟨decodeRow 12 ("70156243", 8), 62⟩, ⟨decodeRow 12 ("01562473", 8), 63⟩, ⟨decodeRow 12 ("15624703", 8), 64⟩, ⟨decodeRow 12 ("56247013", 8), 65⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("62470153", 6), 66⟩, ⟨decodeRow 12 ("36247051", 8), 65⟩, ⟨decodeRow 12 ("62470531", 8), 66⟩, ⟨decodeRow 12 ("24705361", 8), 67⟩])
                  (.leaf [⟨decodeRow 12 ("47053621", 6), 68⟩, ⟨decodeRow 12 ("14705326", 8), 67⟩, ⟨decodeRow 12 ("47053216", 8), 68⟩, ⟨decodeRow 12 ("70532146", 8), 69⟩, ⟨decodeRow 12 ("05321476", 8), 70⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("53214706", 6), 71⟩, ⟨decodeRow 12 ("65321407", 6), 70⟩, ⟨decodeRow 12 ("76532104", 8), 69⟩, ⟨decodeRow 12 ("65321074", 8), 70⟩, ⟨decodeRow 12 ("53210764", 8), 71⟩])
                  (.leaf [⟨decodeRow 12 ("32107654", 8), 72⟩, ⟨decodeRow 12 ("21076534", 6), 73⟩, ⟨decodeRow 12 ("42107635", 8), 72⟩, ⟨decodeRow 12 ("21076345", 8), 73⟩, ⟨decodeRow 12 ("10763425", 8), 74⟩]))))))
        (.branch 76
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("07634215", 6), 75⟩, ⟨decodeRow 12 ("50763412", 8), 74⟩, ⟨decodeRow 12 ("07634152", 8), 75⟩, ⟨decodeRow 12 ("76341502", 6), 76⟩])
                  (.leaf [⟨decodeRow 12 ("27634105", 8), 75⟩, ⟨decodeRow 12 ("76341025", 8), 76⟩, ⟨decodeRow 12 ("63410275", 8), 77⟩, ⟨decodeRow 12 ("34102765", 8), 78⟩, ⟨decodeRow 12 ("41027635", 6), 79⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("54102736", 8), 78⟩, ⟨decodeRow 12 ("41027356", 8), 79⟩, ⟨decodeRow 12 ("10273546", 8), 80⟩, ⟨decodeRow 12 ("02735416", 8), 81⟩, ⟨decodeRow 12 ("27354106", 6), 82⟩])
                  (.leaf [⟨decodeRow 12 ("62735401", 8), 81⟩, ⟨decodeRow 12 ("27354061", 8), 82⟩, ⟨decodeRow 12 ("73540621", 8), 83⟩, ⟨decodeRow 12 ("35406271", 8), 84⟩, ⟨decodeRow 12 ("54062731", 6), 85⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("15406237", 6), 84⟩, ⟨decodeRow 12 ("71540632", 8), 83⟩, ⟨decodeRow 12 ("15406372", 8), 84⟩, ⟨decodeRow 12 ("54063712", 8), 85⟩])
                  (.leaf [⟨decodeRow 12 ("40637152", 8), 86⟩, ⟨decodeRow 12 ("06371542", 6), 87⟩, ⟨decodeRow 12 ("20637145", 8), 86⟩, ⟨decodeRow 12 ("06371425", 8), 87⟩, ⟨decodeRow 12 ("63714205", 8), 88⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("37142065", 6), 89⟩, ⟨decodeRow 12 ("53714260", 8), 88⟩, ⟨decodeRow 12 ("37142650", 8), 89⟩, ⟨decodeRow 12 ("71426530", 8), 90⟩, ⟨decodeRow 12 ("14265370", 8), 91⟩])
                  (.leaf [⟨decodeRow 12 ("42653710", 6), 92⟩, ⟨decodeRow 12 ("04265317", 6), 91⟩, ⟨decodeRow 12 ("70426513", 8), 90⟩, ⟨decodeRow 12 ("04265173", 8), 91⟩, ⟨decodeRow 12 ("42651703", 8), 92⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("26517043", 8), 93⟩, ⟨decodeRow 12 ("65170423", 6), 94⟩, ⟨decodeRow 12 ("36517024", 8), 93⟩, ⟨decodeRow 12 ("65170234", 8), 94⟩])
                  (.leaf [⟨decodeRow 12 ("51702364", 6), 95⟩, ⟨decodeRow 12 ("45170263", 8), 94⟩, ⟨decodeRow 12 ("51702643", 8), 95⟩, ⟨decodeRow 12 ("17026453", 8), 96⟩, ⟨decodeRow 12 ("70264513", 6), 97⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("37026415", 8), 96⟩, ⟨decodeRow 12 ("70264135", 8), 97⟩, ⟨decodeRow 12 ("02641375", 8), 98⟩, ⟨decodeRow 12 ("26413705", 8), 99⟩, ⟨decodeRow 12 ("64137025", 8), 100⟩])
                  (.leaf [⟨decodeRow 12 ("41370265", 6), 101⟩, ⟨decodeRow 12 ("54137062", 8), 100⟩, ⟨decodeRow 12 ("41370652", 8), 101⟩, ⟨decodeRow 12 ("13706542", 8), 102⟩, ⟨decodeRow 12 ("37065412", 6), 103⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("23706514", 8), 102⟩, ⟨decodeRow 12 ("37065124", 8), 103⟩, ⟨decodeRow 12 ("70651234", 8), 104⟩, ⟨decodeRow 12 ("06512374", 8), 105⟩])
                  (.leaf [⟨decodeRow 12 ("65123704", 6), 106⟩, ⟨decodeRow 12 ("46512307", 6), 105⟩, ⟨decodeRow 12 ("74651203", 8), 104⟩, ⟨decodeRow 12 ("46512073", 8), 105⟩, ⟨decodeRow 12 ("65120743", 8), 106⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("51207463", 8), 107⟩, ⟨decodeRow 12 ("12074653", 6), 108⟩, ⟨decodeRow 12 ("31207456", 8), 107⟩, ⟨decodeRow 12 ("12074536", 8), 108⟩, ⟨decodeRow 12 ("20745316", 8), 109⟩])
                  (.leaf [⟨decodeRow 12 ("07453126", 6), 110⟩, ⟨decodeRow 12 ("60745321", 8), 109⟩, ⟨decodeRow 12 ("07453261", 8), 110⟩, ⟨decodeRow 12 ("74532601", 8), 111⟩, ⟨decodeRow 12 ("45326071", 8), 112⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("53260741", 6), 113⟩, ⟨decodeRow 12 ("15326047", 6), 112⟩, ⟨decodeRow 12 ("71532640", 8), 111⟩, ⟨decodeRow 12 ("15326470", 8), 112⟩])
                  (.leaf [⟨decodeRow 12 ("53264710", 8), 113⟩, ⟨decodeRow 12 ("32647150", 6), 114⟩, ⟨decodeRow 12 ("03264751", 8), 113⟩, ⟨decodeRow 12 ("32647501", 8), 114⟩, ⟨decodeRow 12 ("26475031", 8), 115⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("64750321", 6), 116⟩, ⟨decodeRow 12 ("16475023", 8), 115⟩, ⟨decodeRow 12 ("64750213", 8), 116⟩, ⟨decodeRow 12 ("47502163", 8), 117⟩, ⟨decodeRow 12 ("75021643", 8), 118⟩])
                  (.leaf [⟨decodeRow 12 ("50216473", 8), 119⟩, ⟨decodeRow 12 ("02164753", 6), 120⟩, ⟨decodeRow 12 ("30216457", 6), 119⟩, ⟨decodeRow 12 ("73021654", 8), 118⟩, ⟨decodeRow 12 ("30216574", 8), 119⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("02165734", 8), 120⟩, ⟨decodeRow 12 ("21657304", 8), 121⟩, ⟨decodeRow 12 ("16573024", 6), 122⟩, ⟨decodeRow 12 ("41657320", 8), 121⟩])
                  (.leaf [⟨decodeRow 12 ("16573240", 8), 122⟩, ⟨decodeRow 12 ("65732410", 8), 123⟩, ⟨decodeRow 12 ("57324160", 6), 124⟩, ⟨decodeRow 12 ("05732461", 8), 123⟩, ⟨decodeRow 12 ("57324601", 8), 124⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("73246051", 8), 125⟩, ⟨decodeRow 12 ("32460571", 8), 126⟩, ⟨decodeRow 12 ("24605731", 6), 127⟩, ⟨decodeRow 12 ("12460537", 6), 126⟩, ⟨decodeRow 12 ("71246035", 8), 125⟩])
                  (.leaf [⟨decodeRow 12 ("12460375", 8), 126⟩, ⟨decodeRow 12 ("24603715", 8), 127⟩, ⟨decodeRow 12 ("46037125", 8), 128⟩, ⟨decodeRow 12 ("60371245", 6), 129⟩, ⟨decodeRow 12 ("56037142", 8), 128⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("60371452", 8), 129⟩, ⟨decodeRow 12 ("03714562", 8), 130⟩, ⟨decodeRow 12 ("37145602", 6), 131⟩, ⟨decodeRow 12 ("23714506", 8), 130⟩])
                  (.leaf [⟨decodeRow 12 ("37145026", 8), 131⟩, ⟨decodeRow 12 ("71450236", 6), 132⟩, ⟨decodeRow 12 ("67145032", 8), 131⟩, ⟨decodeRow 12 ("71450362", 8), 132⟩, ⟨decodeRow 12 ("14503672", 8), 133⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("45036712", 8), 134⟩, ⟨decodeRow 12 ("50367142", 6), 135⟩, ⟨decodeRow 12 ("25036741", 8), 134⟩, ⟨decodeRow 12 ("50367421", 8), 135⟩, ⟨decodeRow 12 ("03674251", 8), 136⟩])
                  (.leaf [⟨decodeRow 12 ("36742501", 8), 137⟩, ⟨decodeRow 12 ("67425031", 6), 138⟩, ⟨decodeRow 12 ("16742530", 8), 137⟩, ⟨decodeRow 12 ("67425310", 8), 138⟩, ⟨decodeRow 12 ("74253160", 8), 139⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("42531670", 8), 140⟩, ⟨decodeRow 12 ("25316740", 6), 141⟩, ⟨decodeRow 12 ("02531647", 6), 140⟩, ⟨decodeRow 12 ("70253146", 8), 139⟩])
                  (.leaf [⟨decodeRow 12 ("02531476", 8), 140⟩, ⟨decodeRow 12 ("25314706", 8), 141⟩, ⟨decodeRow 12 ("53147026", 8), 142⟩, ⟨decodeRow 12 ("31470256", 6), 143⟩, ⟨decodeRow 12 ("63147052", 8), 142⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("31470562", 8), 143⟩, ⟨decodeRow 12 ("14705632", 8), 144⟩, ⟨decodeRow 12 ("47056312", 6), 145⟩, ⟨decodeRow 12 ("24705613", 8), 144⟩, ⟨decodeRow 12 ("47056123", 8), 145⟩])
                  (.leaf [⟨decodeRow 12 ("70561243", 8), 146⟩, ⟨decodeRow 12 ("05612473", 8), 147⟩, ⟨decodeRow 12 ("56124703", 6), 148⟩, ⟨decodeRow 12 ("35612407", 6), 147⟩, ⟨decodeRow 12 ("73561204", 8), 146⟩])))))))
      (.branch 151
        (.branch 75
          (.branch 37
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("35612074", 8), 147⟩, ⟨decodeRow 12 ("56120734", 8), 148⟩, ⟨decodeRow 12 ("61207354", 8), 149⟩, ⟨decodeRow 12 ("12073564", 6), 150⟩])
                  (.leaf [⟨decodeRow 12 ("41207365", 8), 149⟩, ⟨decodeRow 12 ("12073645", 8), 150⟩, ⟨decodeRow 12 ("20736415", 6), 151⟩, ⟨decodeRow 12 ("52073614", 8), 150⟩, ⟨decodeRow 12 ("20736154", 8), 151⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("07361524", 8), 152⟩, ⟨decodeRow 12 ("73615204", 6), 153⟩, ⟨decodeRow 12 ("47361502", 8), 152⟩, ⟨decodeRow 12 ("73615042", 8), 153⟩])
                  (.leaf [⟨decodeRow 12 ("36150472", 8), 154⟩, ⟨decodeRow 12 ("61504732", 8), 155⟩, ⟨decodeRow 12 ("15047362", 8), 156⟩, ⟨decodeRow 12 ("50473612", 6), 157⟩, ⟨decodeRow 12 ("25047316", 8), 156⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("50473126", 8), 157⟩, ⟨decodeRow 12 ("04731256", 8), 158⟩, ⟨decodeRow 12 ("47312506", 6), 159⟩, ⟨decodeRow 12 ("64731205", 8), 158⟩])
                  (.leaf [⟨decodeRow 12 ("47312065", 8), 159⟩, ⟨decodeRow 12 ("73120645", 8), 160⟩, ⟨decodeRow 12 ("31206475", 8), 161⟩, ⟨decodeRow 12 ("12064735", 6), 162⟩, ⟨decodeRow 12 ("51206437", 6), 161⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("75120634", 8), 160⟩, ⟨decodeRow 12 ("51206374", 8), 161⟩, ⟨decodeRow 12 ("12063754", 8), 162⟩, ⟨decodeRow 12 ("20637514", 8), 163⟩, ⟨decodeRow 12 ("06375124", 6), 164⟩])
                  (.leaf [⟨decodeRow 12 ("40637521", 8), 163⟩, ⟨decodeRow 12 ("06375241", 8), 164⟩, ⟨decodeRow 12 ("63752401", 8), 165⟩, ⟨decodeRow 12 ("37524061", 6), 166⟩, ⟨decodeRow 12 ("13752460", 8), 165⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("37524610", 8), 166⟩, ⟨decodeRow 12 ("75246130", 8), 167⟩, ⟨decodeRow 12 ("52461370", 8), 168⟩, ⟨decodeRow 12 ("24613750", 6), 169⟩])
                  (.leaf [⟨decodeRow 12 ("02461357", 6), 168⟩, ⟨decodeRow 12 ("70246153", 8), 167⟩, ⟨decodeRow 12 ("02461573", 8), 168⟩, ⟨decodeRow 12 ("24615703", 8), 169⟩, ⟨decodeRow 12 ("46157023", 6), 170⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("34615720", 8), 169⟩, ⟨decodeRow 12 ("46157230", 8), 170⟩, ⟨decodeRow 12 ("61572340", 8), 171⟩, ⟨decodeRow 12 ("15723460", 6), 172⟩, ⟨decodeRow 12 ("01572364", 8), 171⟩])
                  (.leaf [⟨decodeRow 12 ("15723604", 8), 172⟩, ⟨decodeRow 12 ("57236014", 8), 173⟩, ⟨decodeRow 12 ("72360154", 8), 174⟩, ⟨decodeRow 12 ("23601574", 8), 175⟩, ⟨decodeRow 12 ("36015724", 6), 176⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("43601527", 6), 175⟩, ⟨decodeRow 12 ("74360125", 8), 174⟩, ⟨decodeRow 12 ("43601275", 8), 175⟩, ⟨decodeRow 12 ("36012745", 8), 176⟩])
                  (.leaf [⟨decodeRow 12 ("60127435", 8), 177⟩, ⟨decodeRow 12 ("01274365", 6), 178⟩, ⟨decodeRow 12 ("50127463", 8), 177⟩, ⟨decodeRow 12 ("01274653", 8), 178⟩, ⟨decodeRow 12 ("12746503", 8), 179⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("27465013", 6), 180⟩, ⟨decodeRow 12 ("32746510", 8), 179⟩, ⟨decodeRow 12 ("27465130", 8), 180⟩, ⟨decodeRow 12 ("74651320", 8), 181⟩, ⟨decodeRow 12 ("46513270", 8), 182⟩])
                  (.leaf [⟨decodeRow 12 ("65132740", 6), 183⟩, ⟨decodeRow 12 ("06513247", 6), 182⟩, ⟨decodeRow 12 ("70651342", 8), 181⟩, ⟨decodeRow 12 ("06513472", 8), 182⟩, ⟨decodeRow 12 ("65134702", 8), 183⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("51347062", 8), 184⟩, ⟨decodeRow 12 ("13470652", 6), 185⟩, ⟨decodeRow 12 ("21347056", 8), 184⟩, ⟨decodeRow 12 ("13470526", 8), 185⟩])
                  (.leaf [⟨decodeRow 12 ("34705216", 8), 186⟩, ⟨decodeRow 12 ("47052136", 6), 187⟩, ⟨decodeRow 12 ("64705231", 8), 186⟩, ⟨decodeRow 12 ("47052361", 8), 187⟩, ⟨decodeRow 12 ("70523641", 6), 188⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("17052346", 8), 187⟩, ⟨decodeRow 12 ("70523416", 8), 188⟩, ⟨decodeRow 12 ("05234176", 8), 189⟩, ⟨decodeRow 12 ("52341706", 8), 190⟩, ⟨decodeRow 12 ("23417056", 6), 191⟩])
                  (.leaf [⟨decodeRow 12 ("62341750", 8), 190⟩, ⟨decodeRow 12 ("23417560", 8), 191⟩, ⟨decodeRow 12 ("34175620", 8), 192⟩, ⟨decodeRow 12 ("41756230", 6), 193⟩, ⟨decodeRow 12 ("04175632", 8), 192⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("41756302", 8), 193⟩, ⟨decodeRow 12 ("17563042", 8), 194⟩, ⟨decodeRow 12 ("75630412", 8), 195⟩, ⟨decodeRow 12 ("56304172", 8), 196⟩])
                  (.leaf [⟨decodeRow 12 ("63041752", 6), 197⟩, ⟨decodeRow 12 ("26304157", 6), 196⟩, ⟨decodeRow 12 ("72630451", 8), 195⟩, ⟨decodeRow 12 ("26304571", 8), 196⟩, ⟨decodeRow 12 ("63045721", 8), 197⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("30457261", 6), 198⟩, ⟨decodeRow 12 ("13045762", 8), 197⟩, ⟨decodeRow 12 ("30457612", 8), 198⟩, ⟨decodeRow 12 ("04576132", 8), 199⟩, ⟨decodeRow 12 ("45761302", 6), 200⟩])
                  (.leaf [⟨decodeRow 12 ("24576103", 8), 199⟩, ⟨decodeRow 12 ("45761023", 8), 200⟩, ⟨decodeRow 12 ("57610243", 8), 201⟩, ⟨decodeRow 12 ("76102453", 6), 202⟩, ⟨decodeRow 12 ("37610254", 8), 201⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76102534", 8), 202⟩, ⟨decodeRow 12 ("61025374", 8), 203⟩, ⟨decodeRow 12 ("10253764", 8), 204⟩, ⟨decodeRow 12 ("02537614", 8), 205⟩])
                  (.leaf [⟨decodeRow 12 ("25376104", 6), 206⟩, ⟨decodeRow 12 ("42537601", 8), 205⟩, ⟨decodeRow 12 ("25376041", 8), 206⟩, ⟨decodeRow 12 ("53760421", 8), 207⟩, ⟨decodeRow 12 ("37604251", 6), 208⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("13760452", 8), 207⟩, ⟨decodeRow 12 ("37604512", 8), 208⟩, ⟨decodeRow 12 ("76045132", 8), 209⟩, ⟨decodeRow 12 ("60451372", 8), 210⟩, ⟨decodeRow 12 ("04513762", 6), 211⟩])
                  (.leaf [⟨decodeRow 12 ("20451367", 6), 210⟩, ⟨decodeRow 12 ("72045163", 8), 209⟩, ⟨decodeRow 12 ("20451673", 8), 210⟩, ⟨decodeRow 12 ("04516723", 8), 211⟩, ⟨decodeRow 12 ("45167203", 8), 212⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("51672043", 6), 213⟩, ⟨decodeRow 12 ("35167240", 8), 212⟩, ⟨decodeRow 12 ("51672430", 8), 213⟩, ⟨decodeRow 12 ("16724350", 8), 214⟩])
                  (.leaf [⟨decodeRow 12 ("67243510", 6), 215⟩, ⟨decodeRow 12 ("06724315", 8), 214⟩, ⟨decodeRow 12 ("67243105", 8), 215⟩, ⟨decodeRow 12 ("72431065", 8), 216⟩, ⟨decodeRow 12 ("24310675", 8), 217⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("43106725", 6), 218⟩, ⟨decodeRow 12 ("54310627", 6), 217⟩, ⟨decodeRow 12 ("75431026", 8), 216⟩, ⟨decodeRow 12 ("54310276", 8), 217⟩, ⟨decodeRow 12 ("43102756", 8), 218⟩])
                  (.leaf [⟨decodeRow 12 ("31027546", 6), 219⟩, ⟨decodeRow 12 ("63102745", 8), 218⟩, ⟨decodeRow 12 ("31027465", 8), 219⟩, ⟨decodeRow 12 ("10274635", 8), 220⟩, ⟨decodeRow 12 ("02746315", 8), 221⟩]))))))
        (.branch 76
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27463105", 6), 222⟩, ⟨decodeRow 12 ("52746301", 8), 221⟩, ⟨decodeRow 12 ("27463051", 8), 222⟩, ⟨decodeRow 12 ("74630521", 8), 223⟩])
                  (.leaf [⟨decodeRow 12 ("46305271", 8), 224⟩, ⟨decodeRow 12 ("63052741", 6), 225⟩, ⟨decodeRow 12 ("16305247", 6), 224⟩, ⟨decodeRow 12 ("71630542", 8), 223⟩, ⟨decodeRow 12 ("16305472", 8), 224⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("63054712", 8), 225⟩, ⟨decodeRow 12 ("30547162", 8), 226⟩, ⟨decodeRow 12 ("05471632", 6), 227⟩, ⟨decodeRow 12 ("20547136", 8), 226⟩, ⟨decodeRow 12 ("05471326", 8), 227⟩])
                  (.leaf [⟨decodeRow 12 ("54713206", 8), 228⟩, ⟨decodeRow 12 ("47132056", 6), 229⟩, ⟨decodeRow 12 ("64713250", 8), 228⟩, ⟨decodeRow 12 ("47132560", 8), 229⟩, ⟨decodeRow 12 ("71325640", 8), 230⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("13256470", 8), 231⟩, ⟨decodeRow 12 ("32564710", 6), 232⟩, ⟨decodeRow 12 ("03256417", 6), 231⟩, ⟨decodeRow 12 ("70325614", 8), 230⟩])
                  (.leaf [⟨decodeRow 12 ("03256174", 8), 231⟩, ⟨decodeRow 12 ("32561704", 8), 232⟩, ⟨decodeRow 12 ("25617034", 8), 233⟩, ⟨decodeRow 12 ("56170324", 6), 234⟩, ⟨decodeRow 12 ("45617023", 8), 233⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("56170243", 8), 234⟩, ⟨decodeRow 12 ("61702453", 6), 235⟩, ⟨decodeRow 12 ("36170254", 8), 234⟩, ⟨decodeRow 12 ("61702534", 8), 235⟩, ⟨decodeRow 12 ("17025364", 8), 236⟩])
                  (.leaf [⟨decodeRow 12 ("70253614", 8), 237⟩, ⟨decodeRow 12 ("02536174", 8), 238⟩, ⟨decodeRow 12 ("25361704", 6), 239⟩, ⟨decodeRow 12 ("42536107", 6), 238⟩, ⟨decodeRow 12 ("74253601", 8), 237⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("42536071", 8), 238⟩, ⟨decodeRow 12 ("25360741", 8), 239⟩, ⟨decodeRow 12 ("53607421", 8), 240⟩, ⟨decodeRow 12 ("36074251", 6), 241⟩])
                  (.leaf [⟨decodeRow 12 ("13607452", 8), 240⟩, ⟨decodeRow 12 ("36074512", 8), 241⟩, ⟨decodeRow 12 ("60745132", 8), 242⟩, ⟨decodeRow 12 ("07451362", 6), 243⟩, ⟨decodeRow 12 ("20745163", 8), 242⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("07451623", 8), 243⟩, ⟨decodeRow 12 ("74516203", 8), 244⟩, ⟨decodeRow 12 ("45162073", 8), 245⟩, ⟨decodeRow 12 ("51620743", 6), 246⟩, ⟨decodeRow 12 ("35162047", 6), 245⟩])
                  (.leaf [⟨decodeRow 12 ("73516240", 8), 244⟩, ⟨decodeRow 12 ("35162470", 8), 245⟩, ⟨decodeRow 12 ("51624730", 8), 246⟩, ⟨decodeRow 12 ("16247350", 8), 247⟩, ⟨decodeRow 12 ("62473510", 6), 248⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("06247315", 8), 247⟩, ⟨decodeRow 12 ("62473105", 8), 248⟩, ⟨decodeRow 12 ("24731065", 8), 249⟩, ⟨decodeRow 12 ("47310625", 6), 250⟩])
                  (.leaf [⟨decodeRow 12 ("54731026", 8), 249⟩, ⟨decodeRow 12 ("47310256", 8), 250⟩, ⟨decodeRow 12 ("73102546", 6), 251⟩, ⟨decodeRow 12 ("67310245", 8), 250⟩, ⟨decodeRow 12 ("73102465", 8), 251⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("31024675", 8), 252⟩, ⟨decodeRow 12 ("10246735", 8), 253⟩, ⟨decodeRow 12 ("02467315", 8), 254⟩, ⟨decodeRow 12 ("24673105", 6), 255⟩, ⟨decodeRow 12 ("52467301", 8), 254⟩])
                  (.leaf [⟨decodeRow 12 ("24673051", 8), 255⟩, ⟨decodeRow 12 ("46730521", 8), 256⟩, ⟨decodeRow 12 ("67305241", 6), 257⟩, ⟨decodeRow 12 ("16730542", 8), 256⟩, ⟨decodeRow 12 ("67305412", 8), 257⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("73054162", 8), 258⟩, ⟨decodeRow 12 ("30541672", 8), 259⟩, ⟨decodeRow 12 ("05416732", 6), 260⟩, ⟨decodeRow 12 ("20541637", 6), 259⟩])
                  (.leaf [⟨decodeRow 12 ("72054136", 8), 258⟩, ⟨decodeRow 12 ("20541376", 8), 259⟩, ⟨decodeRow 12 ("05413726", 8), 260⟩, ⟨decodeRow 12 ("54137206", 8), 261⟩, ⟨decodeRow 12 ("41372056", 6), 262⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("64137250", 8), 261⟩, ⟨decodeRow 12 ("41372560", 8), 262⟩, ⟨decodeRow 12 ("13725640", 8), 263⟩, ⟨decodeRow 12 ("37256410", 6), 264⟩, ⟨decodeRow 12 ("03725614", 8), 263⟩])
                  (.leaf [⟨decodeRow 12 ("37256104", 8), 264⟩, ⟨decodeRow 12 ("72561034", 6), 265⟩, ⟨decodeRow 12 ("47256130", 8), 264⟩, ⟨decodeRow 12 ("72561340", 8), 265⟩, ⟨decodeRow 12 ("25613470", 8), 266⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("56134720", 8), 267⟩, ⟨decodeRow 12 ("61347250", 6), 268⟩, ⟨decodeRow 12 ("06134752", 8), 267⟩, ⟨decodeRow 12 ("61347502", 8), 268⟩])
                  (.leaf [⟨decodeRow 12 ("13475062", 8), 269⟩, ⟨decodeRow 12 ("34750612", 8), 270⟩, ⟨decodeRow 12 ("47506132", 6), 271⟩, ⟨decodeRow 12 ("24750631", 8), 270⟩, ⟨decodeRow 12 ("47506321", 8), 271⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("75063241", 8), 272⟩, ⟨decodeRow 12 ("50632471", 8), 273⟩, ⟨decodeRow 12 ("06324751", 6), 274⟩, ⟨decodeRow 12 ("10632457", 6), 273⟩, ⟨decodeRow 12 ("71063254", 8), 272⟩])
                  (.leaf [⟨decodeRow 12 ("10632574", 8), 273⟩, ⟨decodeRow 12 ("06325714", 8), 274⟩, ⟨decodeRow 12 ("63257104", 8), 275⟩, ⟨decodeRow 12 ("32571064", 6), 276⟩, ⟨decodeRow 12 ("43257160", 8), 275⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("32571640", 8), 276⟩, ⟨decodeRow 12 ("25716430", 8), 277⟩, ⟨decodeRow 12 ("57164320", 6), 278⟩, ⟨decodeRow 12 ("05716423", 8), 277⟩])
                  (.leaf [⟨decodeRow 12 ("57164203", 8), 278⟩, ⟨decodeRow 12 ("71642053", 8), 279⟩, ⟨decodeRow 12 ("16420573", 8), 280⟩, ⟨decodeRow 12 ("64205713", 6), 281⟩, ⟨decodeRow 12 ("36420517", 6), 280⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("73642015", 8), 279⟩, ⟨decodeRow 12 ("36420175", 8), 280⟩, ⟨decodeRow 12 ("64201735", 8), 281⟩, ⟨decodeRow 12 ("42017365", 8), 282⟩, ⟨decodeRow 12 ("20173645", 6), 283⟩])
                  (.leaf [⟨decodeRow 12 ("52017346", 8), 282⟩, ⟨decodeRow 12 ("20173456", 8), 283⟩, ⟨decodeRow 12 ("01734526", 6), 284⟩, ⟨decodeRow 12 ("60173425", 8), 283⟩, ⟨decodeRow 12 ("01734265", 8), 284⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("17342605", 8), 285⟩, ⟨decodeRow 12 ("73426015", 6), 286⟩, ⟨decodeRow 12 ("57342610", 8), 285⟩, ⟨decodeRow 12 ("73426150", 8), 286⟩])
                  (.leaf [⟨decodeRow 12 ("34261570", 8), 287⟩, ⟨decodeRow 12 ("42615730", 8), 288⟩, ⟨decodeRow 12 ("26157340", 6), 289⟩, ⟨decodeRow 12 ("02615743", 8), 288⟩, ⟨decodeRow 12 ("26157403", 8), 289⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("61574023", 8), 290⟩, ⟨decodeRow 12 ("15740263", 8), 291⟩, ⟨decodeRow 12 ("57402613", 6), 292⟩, ⟨decodeRow 12 ("35740216", 8), 291⟩, ⟨decodeRow 12 ("57402136", 8), 292⟩])
                  (.leaf [⟨decodeRow 12 ("74021356", 6), 293⟩, ⟨decodeRow 12 ("67402153", 8), 292⟩, ⟨decodeRow 12 ("74021563", 8), 293⟩, ⟨decodeRow 12 ("40215673", 8), 294⟩, ⟨decodeRow 12 ("02156743", 8), 295⟩]))))))))
    (.branch 303
      (.branch 151
        (.branch 75
          (.branch 37
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("21567403", 6), 296⟩, ⟨decodeRow 12 ("32156704", 8), 295⟩, ⟨decodeRow 12 ("21567034", 8), 296⟩, ⟨decodeRow 12 ("15670324", 8), 297⟩])
                  (.leaf [⟨decodeRow 12 ("56703214", 6), 298⟩, ⟨decodeRow 12 ("45670312", 8), 297⟩, ⟨decodeRow 12 ("56703142", 8), 298⟩, ⟨decodeRow 12 ("67031452", 8), 299⟩, ⟨decodeRow 12 ("70314562", 8), 300⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03145672", 8), 301⟩, ⟨decodeRow 12 ("31456702", 6), 302⟩, ⟨decodeRow 12 ("23145607", 6), 301⟩, ⟨decodeRow 12 ("72314506", 8), 300⟩])
                  (.leaf [⟨decodeRow 12 ("23145076", 8), 301⟩, ⟨decodeRow 12 ("31450726", 8), 302⟩, ⟨decodeRow 12 ("14507236", 6), 303⟩, ⟨decodeRow 12 ("61450732", 8), 302⟩, ⟨decodeRow 12 ("14507362", 8), 303⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45073612", 8), 304⟩, ⟨decodeRow 12 ("50736142", 6), 305⟩, ⟨decodeRow 12 ("25073641", 8), 304⟩, ⟨decodeRow 12 ("50736421", 8), 305⟩])
                  (.leaf [⟨decodeRow 12 ("07364251", 8), 306⟩, ⟨decodeRow 12 ("73642501", 8), 307⟩, ⟨decodeRow 12 ("36425071", 8), 308⟩, ⟨decodeRow 12 ("64250731", 6), 309⟩, ⟨decodeRow 12 ("16425037", 6), 308⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("71642530", 8), 307⟩, ⟨decodeRow 12 ("16425370", 8), 308⟩, ⟨decodeRow 12 ("64253710", 8), 309⟩, ⟨decodeRow 12 ("42537160", 8), 310⟩, ⟨decodeRow 12 ("25371640", 6), 311⟩])
                  (.leaf [⟨decodeRow 12 ("02537146", 8), 310⟩, ⟨decodeRow 12 ("25371406", 8), 311⟩, ⟨decodeRow 12 ("53714026", 8), 312⟩, ⟨decodeRow 12 ("37140256", 6), 313⟩, ⟨decodeRow 12 ("63714052", 8), 312⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("37140562", 8), 313⟩, ⟨decodeRow 12 ("71405632", 8), 314⟩, ⟨decodeRow 12 ("14056372", 8), 315⟩, ⟨decodeRow 12 ("40563712", 6), 316⟩])
                  (.leaf [⟨decodeRow 12 ("24056317", 6), 315⟩, ⟨decodeRow 12 ("72405613", 8), 314⟩, ⟨decodeRow 12 ("24056173", 8), 315⟩, ⟨decodeRow 12 ("40561723", 8), 316⟩, ⟨decodeRow 12 ("05617243", 8), 317⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("56172403", 6), 318⟩, ⟨decodeRow 12 ("35617204", 8), 317⟩, ⟨decodeRow 12 ("56172034", 8), 318⟩, ⟨decodeRow 12 ("61720354", 8), 319⟩, ⟨decodeRow 12 ("17203564", 6), 320⟩])
                  (.leaf [⟨decodeRow 12 ("41720365", 8), 319⟩, ⟨decodeRow 12 ("17203645", 8), 320⟩, ⟨decodeRow 12 ("72036415", 6), 321⟩, ⟨decodeRow 12 ("57203614", 8), 320⟩, ⟨decodeRow 12 ("72036154", 8), 321⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("20361574", 8), 322⟩, ⟨decodeRow 12 ("03615724", 8), 323⟩, ⟨decodeRow 12 ("36157204", 6), 324⟩, ⟨decodeRow 12 ("43615702", 8), 323⟩])
                  (.leaf [⟨decodeRow 12 ("36157042", 8), 324⟩, ⟨decodeRow 12 ("61570432", 8), 325⟩, ⟨decodeRow 12 ("15704362", 6), 326⟩, ⟨decodeRow 12 ("21570463", 8), 325⟩, ⟨decodeRow 12 ("15704623", 8), 326⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("57046213", 8), 327⟩, ⟨decodeRow 12 ("70462153", 8), 328⟩, ⟨decodeRow 12 ("04621573", 8), 329⟩, ⟨decodeRow 12 ("46215703", 6), 330⟩, ⟨decodeRow 12 ("34621507", 6), 329⟩])
                  (.leaf [⟨decodeRow 12 ("73462105", 8), 328⟩, ⟨decodeRow 12 ("34621075", 8), 329⟩, ⟨decodeRow 12 ("46210735", 8), 330⟩, ⟨decodeRow 12 ("62107345", 6), 331⟩, ⟨decodeRow 12 ("56210743", 8), 330⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("62107453", 8), 331⟩, ⟨decodeRow 12 ("21074563", 8), 332⟩, ⟨decodeRow 12 ("10745623", 6), 333⟩, ⟨decodeRow 12 ("31074526", 8), 332⟩])
                  (.leaf [⟨decodeRow 12 ("10745236", 8), 333⟩, ⟨decodeRow 12 ("07452316", 8), 334⟩, ⟨decodeRow 12 ("74523106", 8), 335⟩, ⟨decodeRow 12 ("45231076", 8), 336⟩, ⟨decodeRow 12 ("52310746", 6), 337⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("65231047", 6), 336⟩, ⟨decodeRow 12 ("76523140", 8), 335⟩, ⟨decodeRow 12 ("65231470", 8), 336⟩, ⟨decodeRow 12 ("52314760", 8), 337⟩, ⟨decodeRow 12 ("23147650", 8), 338⟩])
                  (.leaf [⟨decodeRow 12 ("31476520", 6), 339⟩, ⟨decodeRow 12 ("03147625", 8), 338⟩, ⟨decodeRow 12 ("31476205", 8), 339⟩, ⟨decodeRow 12 ("14762035", 8), 340⟩, ⟨decodeRow 12 ("47620315", 6), 341⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54762013", 8), 340⟩, ⟨decodeRow 12 ("47620153", 8), 341⟩, ⟨decodeRow 12 ("76201543", 8), 342⟩, ⟨decodeRow 12 ("62015473", 8), 343⟩])
                  (.leaf [⟨decodeRow 12 ("20154763", 6), 344⟩, ⟨decodeRow 12 ("32015467", 6), 343⟩, ⟨decodeRow 12 ("73201564", 8), 342⟩, ⟨decodeRow 12 ("32015674", 8), 343⟩, ⟨decodeRow 12 ("20156734", 8), 344⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("01567324", 6), 345⟩, ⟨decodeRow 12 ("40156723", 8), 344⟩, ⟨decodeRow 12 ("01567243", 8), 345⟩, ⟨decodeRow 12 ("15672403", 8), 346⟩, ⟨decodeRow 12 ("56724013", 8), 347⟩])
                  (.leaf [⟨decodeRow 12 ("67240153", 6), 348⟩, ⟨decodeRow 12 ("36724051", 8), 347⟩, ⟨decodeRow 12 ("67240531", 8), 348⟩, ⟨decodeRow 12 ("72405361", 8), 349⟩, ⟨decodeRow 12 ("24053671", 8), 350⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40536721", 6), 351⟩, ⟨decodeRow 12 ("14053627", 6), 350⟩, ⟨decodeRow 12 ("71405326", 8), 349⟩, ⟨decodeRow 12 ("14053276", 8), 350⟩])
                  (.leaf [⟨decodeRow 12 ("40532716", 8), 351⟩, ⟨decodeRow 12 ("05327146", 8), 352⟩, ⟨decodeRow 12 ("53271406", 6), 353⟩, ⟨decodeRow 12 ("65327104", 8), 352⟩, ⟨decodeRow 12 ("53271064", 8), 353⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("32710654", 8), 354⟩, ⟨decodeRow 12 ("27106534", 6), 355⟩, ⟨decodeRow 12 ("42710635", 8), 354⟩, ⟨decodeRow 12 ("27106345", 8), 355⟩, ⟨decodeRow 12 ("71063425", 8), 356⟩])
                  (.leaf [⟨decodeRow 12 ("10634275", 8), 357⟩, ⟨decodeRow 12 ("06342715", 6), 358⟩, ⟨decodeRow 12 ("50634217", 6), 357⟩, ⟨decodeRow 12 ("75063412", 8), 356⟩, ⟨decodeRow 12 ("50634172", 8), 357⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("06341752", 8), 358⟩, ⟨decodeRow 12 ("63417502", 6), 359⟩, ⟨decodeRow 12 ("26341705", 8), 358⟩, ⟨decodeRow 12 ("63417025", 8), 359⟩])
                  (.leaf [⟨decodeRow 12 ("34170265", 8), 360⟩, ⟨decodeRow 12 ("41702635", 6), 361⟩, ⟨decodeRow 12 ("54170236", 8), 360⟩, ⟨decodeRow 12 ("41702356", 8), 361⟩, ⟨decodeRow 12 ("17023546", 8), 362⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("70235416", 8), 363⟩, ⟨decodeRow 12 ("02354176", 8), 364⟩, ⟨decodeRow 12 ("23541706", 6), 365⟩, ⟨decodeRow 12 ("62354107", 6), 364⟩, ⟨decodeRow 12 ("76235401", 8), 363⟩])
                  (.leaf [⟨decodeRow 12 ("62354071", 8), 364⟩, ⟨decodeRow 12 ("23540761", 8), 365⟩, ⟨decodeRow 12 ("35407621", 8), 366⟩, ⟨decodeRow 12 ("54076231", 6), 367⟩, ⟨decodeRow 12 ("15407632", 8), 366⟩]))))))
        (.branch 76
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54076312", 8), 367⟩, ⟨decodeRow 12 ("40763152", 8), 368⟩, ⟨decodeRow 12 ("07631542", 6), 369⟩, ⟨decodeRow 12 ("20763145", 8), 368⟩])
                  (.leaf [⟨decodeRow 12 ("07631425", 8), 369⟩, ⟨decodeRow 12 ("76314205", 8), 370⟩, ⟨decodeRow 12 ("63142075", 8), 371⟩, ⟨decodeRow 12 ("31420765", 6), 372⟩, ⟨decodeRow 12 ("53142067", 6), 371⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("75314260", 8), 370⟩, ⟨decodeRow 12 ("53142670", 8), 371⟩, ⟨decodeRow 12 ("31426750", 8), 372⟩, ⟨decodeRow 12 ("14267530", 8), 373⟩, ⟨decodeRow 12 ("42675310", 6), 374⟩])
                  (.leaf [⟨decodeRow 12 ("04267513", 8), 373⟩, ⟨decodeRow 12 ("42675103", 8), 374⟩, ⟨decodeRow 12 ("26751043", 8), 375⟩, ⟨decodeRow 12 ("67510423", 6), 376⟩, ⟨decodeRow 12 ("36751024", 8), 375⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67510234", 8), 376⟩, ⟨decodeRow 12 ("75102364", 6), 377⟩, ⟨decodeRow 12 ("47510263", 8), 376⟩, ⟨decodeRow 12 ("75102643", 8), 377⟩])
                  (.leaf [⟨decodeRow 12 ("51026473", 8), 378⟩, ⟨decodeRow 12 ("10264753", 8), 379⟩, ⟨decodeRow 12 ("02647513", 6), 380⟩, ⟨decodeRow 12 ("30264715", 8), 379⟩, ⟨decodeRow 12 ("02647135", 8), 380⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("26471305", 8), 381⟩, ⟨decodeRow 12 ("64713025", 8), 382⟩, ⟨decodeRow 12 ("47130265", 6), 383⟩, ⟨decodeRow 12 ("54713062", 8), 382⟩, ⟨decodeRow 12 ("47130652", 8), 383⟩])
                  (.leaf [⟨decodeRow 12 ("71306542", 8), 384⟩, ⟨decodeRow 12 ("13065472", 8), 385⟩, ⟨decodeRow 12 ("30654712", 6), 386⟩, ⟨decodeRow 12 ("23065417", 6), 385⟩, ⟨decodeRow 12 ("72306514", 8), 384⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("23065174", 8), 385⟩, ⟨decodeRow 12 ("30651724", 8), 386⟩, ⟨decodeRow 12 ("06517234", 8), 387⟩, ⟨decodeRow 12 ("65172304", 6), 388⟩])
                  (.leaf [⟨decodeRow 12 ("46517203", 8), 387⟩, ⟨decodeRow 12 ("65172043", 8), 388⟩, ⟨decodeRow 12 ("51720463", 8), 389⟩, ⟨decodeRow 12 ("17204653", 6), 390⟩, ⟨decodeRow 12 ("31720456", 8), 389⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("17204536", 8), 390⟩, ⟨decodeRow 12 ("72045316", 8), 391⟩, ⟨decodeRow 12 ("20453176", 8), 392⟩, ⟨decodeRow 12 ("04531726", 6), 393⟩, ⟨decodeRow 12 ("60453127", 6), 392⟩])
                  (.leaf [⟨decodeRow 12 ("76045321", 8), 391⟩, ⟨decodeRow 12 ("60453271", 8), 392⟩, ⟨decodeRow 12 ("04532761", 8), 393⟩, ⟨decodeRow 12 ("45327601", 8), 394⟩, ⟨decodeRow 12 ("53276041", 6), 395⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("15327640", 8), 394⟩, ⟨decodeRow 12 ("53276410", 8), 395⟩, ⟨decodeRow 12 ("32764150", 6), 396⟩, ⟨decodeRow 12 ("03276451", 8), 395⟩])
                  (.leaf [⟨decodeRow 12 ("32764501", 8), 396⟩, ⟨decodeRow 12 ("27645031", 8), 397⟩, ⟨decodeRow 12 ("76450321", 6), 398⟩, ⟨decodeRow 12 ("17645023", 8), 397⟩, ⟨decodeRow 12 ("76450213", 8), 398⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("64502173", 8), 399⟩, ⟨decodeRow 12 ("45021763", 8), 400⟩, ⟨decodeRow 12 ("50217643", 8), 401⟩, ⟨decodeRow 12 ("02176453", 6), 402⟩, ⟨decodeRow 12 ("30217654", 8), 401⟩])
                  (.leaf [⟨decodeRow 12 ("02176534", 8), 402⟩, ⟨decodeRow 12 ("21765304", 8), 403⟩, ⟨decodeRow 12 ("17653024", 6), 404⟩, ⟨decodeRow 12 ("41765320", 8), 403⟩, ⟨decodeRow 12 ("17653240", 8), 404⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76532410", 8), 405⟩, ⟨decodeRow 12 ("65324170", 8), 406⟩, ⟨decodeRow 12 ("53241760", 6), 407⟩, ⟨decodeRow 12 ("05324167", 6), 406⟩])
                  (.leaf [⟨decodeRow 12 ("70532461", 8), 405⟩, ⟨decodeRow 12 ("05324671", 8), 406⟩, ⟨decodeRow 12 ("53246701", 8), 407⟩, ⟨decodeRow 12 ("32467051", 8), 408⟩, ⟨decodeRow 12 ("24670531", 6), 409⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("12467035", 8), 408⟩, ⟨decodeRow 12 ("24670315", 8), 409⟩, ⟨decodeRow 12 ("46703125", 6), 410⟩, ⟨decodeRow 12 ("54670321", 8), 409⟩, ⟨decodeRow 12 ("46703251", 8), 410⟩])
                  (.leaf [⟨decodeRow 12 ("67032541", 8), 411⟩, ⟨decodeRow 12 ("70325461", 8), 412⟩, ⟨decodeRow 12 ("03254671", 8), 413⟩, ⟨decodeRow 12 ("32546701", 6), 414⟩, ⟨decodeRow 12 ("13254607", 6), 413⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("71325406", 8), 412⟩, ⟨decodeRow 12 ("13254076", 8), 413⟩, ⟨decodeRow 12 ("32540716", 8), 414⟩, ⟨decodeRow 12 ("25407136", 8), 415⟩])
                  (.leaf [⟨decodeRow 12 ("54071326", 6), 416⟩, ⟨decodeRow 12 ("65407123", 8), 415⟩, ⟨decodeRow 12 ("54071263", 8), 416⟩, ⟨decodeRow 12 ("40712653", 8), 417⟩, ⟨decodeRow 12 ("07126543", 6), 418⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("30712645", 8), 417⟩, ⟨decodeRow 12 ("07126435", 8), 418⟩, ⟨decodeRow 12 ("71264305", 8), 419⟩, ⟨decodeRow 12 ("12643075", 8), 420⟩, ⟨decodeRow 12 ("26430715", 6), 421⟩])
                  (.leaf [⟨decodeRow 12 ("52643017", 6), 420⟩, ⟨decodeRow 12 ("75264310", 8), 419⟩, ⟨decodeRow 12 ("52643170", 8), 420⟩, ⟨decodeRow 12 ("26431750", 8), 421⟩, ⟨decodeRow 12 ("64317520", 8), 422⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("43175260", 6), 423⟩, ⟨decodeRow 12 ("04317562", 8), 422⟩, ⟨decodeRow 12 ("43175602", 8), 423⟩, ⟨decodeRow 12 ("31756042", 6), 424⟩])
                  (.leaf [⟨decodeRow 12 ("23175640", 8), 423⟩, ⟨decodeRow 12 ("31756420", 8), 424⟩, ⟨decodeRow 12 ("17564230", 8), 425⟩, ⟨decodeRow 12 ("75642310", 6), 426⟩, ⟨decodeRow 12 ("07564213", 8), 425⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("75642103", 8), 426⟩, ⟨decodeRow 12 ("56421073", 8), 427⟩, ⟨decodeRow 12 ("64210753", 8), 428⟩, ⟨decodeRow 12 ("42107563", 8), 429⟩, ⟨decodeRow 12 ("21075643", 6), 430⟩])
                  (.leaf [⟨decodeRow 12 ("32107546", 8), 429⟩, ⟨decodeRow 12 ("21075436", 8), 430⟩, ⟨decodeRow 12 ("10754326", 8), 431⟩, ⟨decodeRow 12 ("07543216", 6), 432⟩, ⟨decodeRow 12 ("60754312", 8), 431⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("07543162", 8), 432⟩, ⟨decodeRow 12 ("75431602", 8), 433⟩, ⟨decodeRow 12 ("54316072", 8), 434⟩, ⟨decodeRow 12 ("43160752", 6), 435⟩])
                  (.leaf [⟨decodeRow 12 ("24316057", 6), 434⟩, ⟨decodeRow 12 ("72431650", 8), 433⟩, ⟨decodeRow 12 ("24316570", 8), 434⟩, ⟨decodeRow 12 ("43165720", 8), 435⟩, ⟨decodeRow 12 ("31657240", 8), 436⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("16572430", 6), 437⟩, ⟨decodeRow 12 ("01657234", 8), 436⟩, ⟨decodeRow 12 ("16572304", 8), 437⟩, ⟨decodeRow 12 ("65723014", 8), 438⟩, ⟨decodeRow 12 ("57230164", 6), 439⟩])
                  (.leaf [⟨decodeRow 12 ("45723061", 8), 438⟩, ⟨decodeRow 12 ("57230641", 8), 439⟩, ⟨decodeRow 12 ("72306451", 8), 440⟩, ⟨decodeRow 12 ("23064571", 8), 441⟩, ⟨decodeRow 12 ("30645721", 6), 442⟩])))))))
      (.branch 151
        (.branch 75
          (.branch 37
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("13064527", 6), 441⟩, ⟨decodeRow 12 ("71306425", 8), 440⟩, ⟨decodeRow 12 ("13064275", 8), 441⟩, ⟨decodeRow 12 ("30642715", 8), 442⟩])
                  (.leaf [⟨decodeRow 12 ("06427135", 6), 443⟩, ⟨decodeRow 12 ("50642731", 8), 442⟩, ⟨decodeRow 12 ("06427351", 8), 443⟩, ⟨decodeRow 12 ("64273501", 8), 444⟩, ⟨decodeRow 12 ("42735061", 6), 445⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14273560", 8), 444⟩, ⟨decodeRow 12 ("42735610", 8), 445⟩, ⟨decodeRow 12 ("27356140", 8), 446⟩, ⟨decodeRow 12 ("73561420", 8), 447⟩])
                  (.leaf [⟨decodeRow 12 ("35614270", 8), 448⟩, ⟨decodeRow 12 ("56142730", 6), 449⟩, ⟨decodeRow 12 ("05614237", 6), 448⟩, ⟨decodeRow 12 ("70561432", 8), 447⟩, ⟨decodeRow 12 ("05614372", 8), 448⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("56143702", 8), 449⟩, ⟨decodeRow 12 ("61437052", 8), 450⟩, ⟨decodeRow 12 ("14370562", 6), 451⟩, ⟨decodeRow 12 ("21437065", 8), 450⟩])
                  (.leaf [⟨decodeRow 12 ("14370625", 8), 451⟩, ⟨decodeRow 12 ("43706215", 6), 452⟩, ⟨decodeRow 12 ("54370612", 8), 451⟩, ⟨decodeRow 12 ("43706152", 8), 452⟩, ⟨decodeRow 12 ("37061542", 8), 453⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("70615432", 8), 454⟩, ⟨decodeRow 12 ("06154372", 8), 455⟩, ⟨decodeRow 12 ("61543702", 6), 456⟩, ⟨decodeRow 12 ("26154307", 6), 455⟩, ⟨decodeRow 12 ("72615403", 8), 454⟩])
                  (.leaf [⟨decodeRow 12 ("26154073", 8), 455⟩, ⟨decodeRow 12 ("61540723", 8), 456⟩, ⟨decodeRow 12 ("15407263", 8), 457⟩, ⟨decodeRow 12 ("54072613", 6), 458⟩, ⟨decodeRow 12 ("35407216", 8), 457⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54072136", 8), 458⟩, ⟨decodeRow 12 ("40721356", 6), 459⟩, ⟨decodeRow 12 ("64072153", 8), 458⟩, ⟨decodeRow 12 ("40721563", 8), 459⟩])
                  (.leaf [⟨decodeRow 12 ("07215643", 8), 460⟩, ⟨decodeRow 12 ("72156403", 6), 461⟩, ⟨decodeRow 12 ("37215604", 8), 460⟩, ⟨decodeRow 12 ("72156034", 8), 461⟩, ⟨decodeRow 12 ("21560374", 8), 462⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("15603724", 8), 463⟩, ⟨decodeRow 12 ("56037214", 8), 464⟩, ⟨decodeRow 12 ("60372154", 6), 465⟩, ⟨decodeRow 12 ("46037251", 8), 464⟩, ⟨decodeRow 12 ("60372541", 8), 465⟩])
                  (.leaf [⟨decodeRow 12 ("03725461", 8), 466⟩, ⟨decodeRow 12 ("37254601", 6), 467⟩, ⟨decodeRow 12 ("13725406", 8), 466⟩, ⟨decodeRow 12 ("37254016", 8), 467⟩, ⟨decodeRow 12 ("72540136", 8), 468⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("25401376", 8), 469⟩, ⟨decodeRow 12 ("54013726", 6), 470⟩, ⟨decodeRow 12 ("65401327", 6), 469⟩, ⟨decodeRow 12 ("76540123", 8), 468⟩])
                  (.leaf [⟨decodeRow 12 ("65401273", 8), 469⟩, ⟨decodeRow 12 ("54012763", 8), 470⟩, ⟨decodeRow 12 ("40127653", 8), 471⟩, ⟨decodeRow 12 ("01276543", 6), 472⟩, ⟨decodeRow 12 ("30127645", 8), 471⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("01276435", 8), 472⟩, ⟨decodeRow 12 ("12764305", 8), 473⟩, ⟨decodeRow 12 ("27643015", 6), 474⟩, ⟨decodeRow 12 ("52764310", 8), 473⟩, ⟨decodeRow 12 ("27643150", 8), 474⟩])
                  (.leaf [⟨decodeRow 12 ("76431520", 8), 475⟩, ⟨decodeRow 12 ("64315270", 8), 476⟩, ⟨decodeRow 12 ("43152760", 6), 477⟩, ⟨decodeRow 12 ("04315267", 6), 476⟩, ⟨decodeRow 12 ("70431562", 8), 475⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("04315672", 8), 476⟩, ⟨decodeRow 12 ("43156702", 8), 477⟩, ⟨decodeRow 12 ("31567042", 6), 478⟩, ⟨decodeRow 12 ("23156740", 8), 477⟩])
                  (.leaf [⟨decodeRow 12 ("31567420", 8), 478⟩, ⟨decodeRow 12 ("15674230", 8), 479⟩, ⟨decodeRow 12 ("56742310", 6), 480⟩, ⟨decodeRow 12 ("05674213", 8), 479⟩, ⟨decodeRow 12 ("56742103", 8), 480⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("67421053", 8), 481⟩, ⟨decodeRow 12 ("74210563", 8), 482⟩, ⟨decodeRow 12 ("42105673", 8), 483⟩, ⟨decodeRow 12 ("21056743", 6), 484⟩, ⟨decodeRow 12 ("32105647", 6), 483⟩])
                  (.leaf [⟨decodeRow 12 ("73210546", 8), 482⟩, ⟨decodeRow 12 ("32105476", 8), 483⟩, ⟨decodeRow 12 ("21054736", 8), 484⟩, ⟨decodeRow 12 ("10547326", 8), 485⟩, ⟨decodeRow 12 ("05473216", 6), 486⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("60547312", 8), 485⟩, ⟨decodeRow 12 ("05473162", 8), 486⟩, ⟨decodeRow 12 ("54731602", 8), 487⟩, ⟨decodeRow 12 ("47316052", 6), 488⟩])
                  (.leaf [⟨decodeRow 12 ("24731650", 8), 487⟩, ⟨decodeRow 12 ("47316520", 8), 488⟩, ⟨decodeRow 12 ("73165240", 8), 489⟩, ⟨decodeRow 12 ("31652470", 8), 490⟩, ⟨decodeRow 12 ("16524730", 6), 491⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("01652437", 6), 490⟩, ⟨decodeRow 12 ("70165234", 8), 489⟩, ⟨decodeRow 12 ("01652374", 8), 490⟩, ⟨decodeRow 12 ("16523704", 8), 491⟩, ⟨decodeRow 12 ("65237014", 8), 492⟩])
                  (.leaf [⟨decodeRow 12 ("52370164", 6), 493⟩, ⟨decodeRow 12 ("45237061", 8), 492⟩, ⟨decodeRow 12 ("52370641", 8), 493⟩, ⟨decodeRow 12 ("23706451", 8), 494⟩, ⟨decodeRow 12 ("37064521", 6), 495⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("13706425", 8), 494⟩, ⟨decodeRow 12 ("37064215", 8), 495⟩, ⟨decodeRow 12 ("70642135", 6), 496⟩, ⟨decodeRow 12 ("57064231", 8), 495⟩])
                  (.leaf [⟨decodeRow 12 ("70642351", 8), 496⟩, ⟨decodeRow 12 ("06423571", 8), 497⟩, ⟨decodeRow 12 ("64235701", 8), 498⟩, ⟨decodeRow 12 ("42357061", 6), 499⟩, ⟨decodeRow 12 ("14235760", 8), 498⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("42357610", 8), 499⟩, ⟨decodeRow 12 ("23576140", 8), 500⟩, ⟨decodeRow 12 ("35761420", 8), 501⟩, ⟨decodeRow 12 ("57614230", 6), 502⟩, ⟨decodeRow 12 ("05761432", 8), 501⟩])
                  (.leaf [⟨decodeRow 12 ("57614302", 8), 502⟩, ⟨decodeRow 12 ("76143052", 8), 503⟩, ⟨decodeRow 12 ("61430572", 8), 504⟩, ⟨decodeRow 12 ("14305762", 6), 505⟩, ⟨decodeRow 12 ("21430567", 6), 504⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("72143065", 8), 503⟩, ⟨decodeRow 12 ("21430675", 8), 504⟩, ⟨decodeRow 12 ("14306725", 8), 505⟩, ⟨decodeRow 12 ("43067215", 6), 506⟩])
                  (.leaf [⟨decodeRow 12 ("54306712", 8), 505⟩, ⟨decodeRow 12 ("43067152", 8), 506⟩, ⟨decodeRow 12 ("30671542", 8), 507⟩, ⟨decodeRow 12 ("06715432", 6), 508⟩, ⟨decodeRow 12 ("20671534", 8), 507⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("06715324", 8), 508⟩, ⟨decodeRow 12 ("67153204", 8), 509⟩, ⟨decodeRow 12 ("71532064", 8), 510⟩, ⟨decodeRow 12 ("15320674", 8), 511⟩, ⟨decodeRow 12 ("53206714", 6), 512⟩])
                  (.leaf [⟨decodeRow 12 ("45320617", 6), 511⟩, ⟨decodeRow 12 ("74532016", 8), 510⟩, ⟨decodeRow 12 ("45320176", 8), 511⟩, ⟨decodeRow 12 ("53201746", 8), 512⟩, ⟨decodeRow 12 ("32017456", 8), 513⟩]))))))
        (.branch 76
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("20174536", 6), 514⟩, ⟨decodeRow 12 ("62017435", 8), 513⟩, ⟨decodeRow 12 ("20174365", 8), 514⟩, ⟨decodeRow 12 ("01743625", 8), 515⟩])
                  (.leaf [⟨decodeRow 12 ("17436205", 6), 516⟩, ⟨decodeRow 12 ("51743602", 8), 515⟩, ⟨decodeRow 12 ("17436052", 8), 516⟩, ⟨decodeRow 12 ("74360512", 8), 517⟩, ⟨decodeRow 12 ("43605172", 8), 518⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("36051742", 6), 519⟩, ⟨decodeRow 12 ("23605147", 6), 518⟩, ⟨decodeRow 12 ("72360541", 8), 517⟩, ⟨decodeRow 12 ("23605471", 8), 518⟩, ⟨decodeRow 12 ("36054721", 8), 519⟩])
                  (.leaf [⟨decodeRow 12 ("60547231", 8), 520⟩, ⟨decodeRow 12 ("05472361", 6), 521⟩, ⟨decodeRow 12 ("10547263", 8), 520⟩, ⟨decodeRow 12 ("05472613", 8), 521⟩, ⟨decodeRow 12 ("54726103", 6), 522⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("35472601", 8), 521⟩, ⟨decodeRow 12 ("54726031", 8), 522⟩, ⟨decodeRow 12 ("47260351", 8), 523⟩, ⟨decodeRow 12 ("72603541", 6), 524⟩])
                  (.leaf [⟨decodeRow 12 ("17260345", 8), 523⟩, ⟨decodeRow 12 ("72603415", 8), 524⟩, ⟨decodeRow 12 ("26034175", 8), 525⟩, ⟨decodeRow 12 ("60341725", 8), 526⟩, ⟨decodeRow 12 ("03417265", 8), 527⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("34172605", 6), 528⟩, ⟨decodeRow 12 ("53417206", 8), 527⟩, ⟨decodeRow 12 ("34172056", 8), 528⟩, ⟨decodeRow 12 ("41720536", 8), 529⟩, ⟨decodeRow 12 ("17205346", 6), 530⟩])
                  (.leaf [⟨decodeRow 12 ("61720543", 8), 529⟩, ⟨decodeRow 12 ("17205463", 8), 530⟩, ⟨decodeRow 12 ("72054613", 8), 531⟩, ⟨decodeRow 12 ("20546173", 8), 532⟩, ⟨decodeRow 12 ("05461723", 6), 533⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("30546127", 6), 532⟩, ⟨decodeRow 12 ("73054621", 8), 531⟩, ⟨decodeRow 12 ("30546271", 8), 532⟩, ⟨decodeRow 12 ("05462731", 8), 533⟩])
                  (.leaf [⟨decodeRow 12 ("54627301", 8), 534⟩, ⟨decodeRow 12 ("46273051", 6), 535⟩, ⟨decodeRow 12 ("14627350", 8), 534⟩, ⟨decodeRow 12 ("46273510", 8), 535⟩, ⟨decodeRow 12 ("62735140", 8), 536⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("27351460", 6), 537⟩, ⟨decodeRow 12 ("02735164", 8), 536⟩, ⟨decodeRow 12 ("27351604", 8), 537⟩, ⟨decodeRow 12 ("73516024", 8), 538⟩, ⟨decodeRow 12 ("35160274", 8), 539⟩])
                  (.leaf [⟨decodeRow 12 ("51602734", 6), 540⟩, ⟨decodeRow 12 ("45160237", 6), 539⟩, ⟨decodeRow 12 ("74516032", 8), 538⟩, ⟨decodeRow 12 ("45160372", 8), 539⟩, ⟨decodeRow 12 ("51603742", 8), 540⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("16037452", 6), 541⟩, ⟨decodeRow 12 ("21603754", 8), 540⟩, ⟨decodeRow 12 ("16037524", 8), 541⟩, ⟨decodeRow 12 ("60375214", 8), 542⟩])
                  (.leaf [⟨decodeRow 12 ("03752164", 6), 543⟩, ⟨decodeRow 12 ("40375261", 8), 542⟩, ⟨decodeRow 12 ("03752641", 8), 543⟩, ⟨decodeRow 12 ("37526401", 8), 544⟩, ⟨decodeRow 12 ("75264031", 8), 545⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("52640371", 8), 546⟩, ⟨decodeRow 12 ("26403751", 6), 547⟩, ⟨decodeRow 12 ("12640357", 6), 546⟩, ⟨decodeRow 12 ("71264053", 8), 545⟩, ⟨decodeRow 12 ("12640573", 8), 546⟩])
                  (.leaf [⟨decodeRow 12 ("26405713", 8), 547⟩, ⟨decodeRow 12 ("64057123", 8), 548⟩, ⟨decodeRow 12 ("40571263", 6), 549⟩, ⟨decodeRow 12 ("34057162", 8), 548⟩, ⟨decodeRow 12 ("40571632", 8), 549⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("05716342", 8), 550⟩, ⟨decodeRow 12 ("57163402", 6), 551⟩, ⟨decodeRow 12 ("25716304", 8), 550⟩, ⟨decodeRow 12 ("57163024", 8), 551⟩])
                  (.leaf [⟨decodeRow 12 ("71630254", 8), 552⟩, ⟨decodeRow 12 ("16302574", 8), 553⟩, ⟨decodeRow 12 ("63025714", 6), 554⟩, ⟨decodeRow 12 ("46302517", 6), 553⟩, ⟨decodeRow 12 ("74630215", 8), 552⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("46302175", 8), 553⟩, ⟨decodeRow 12 ("63021745", 8), 554⟩, ⟨decodeRow 12 ("30217465", 8), 555⟩, ⟨decodeRow 12 ("02174635", 6), 556⟩, ⟨decodeRow 12 ("50217436", 8), 555⟩])
                  (.leaf [⟨decodeRow 12 ("02174356", 8), 556⟩, ⟨decodeRow 12 ("21743506", 8), 557⟩, ⟨decodeRow 12 ("17435026", 6), 558⟩, ⟨decodeRow 12 ("61743520", 8), 557⟩, ⟨decodeRow 12 ("17435260", 8), 558⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74352610", 6), 559⟩, ⟨decodeRow 12 ("07435216", 8), 558⟩, ⟨decodeRow 12 ("74352106", 8), 559⟩, ⟨decodeRow 12 ("43521076", 8), 560⟩])
                  (.leaf [⟨decodeRow 12 ("35210746", 8), 561⟩, ⟨decodeRow 12 ("52107436", 6), 562⟩, ⟨decodeRow 12 ("65210734", 8), 561⟩, ⟨decodeRow 12 ("52107364", 8), 562⟩, ⟨decodeRow 12 ("21073654", 8), 563⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("10736524", 6), 564⟩, ⟨decodeRow 12 ("41073625", 8), 563⟩, ⟨decodeRow 12 ("10736245", 8), 564⟩, ⟨decodeRow 12 ("07362415", 8), 565⟩, ⟨decodeRow 12 ("73624105", 8), 566⟩])
                  (.leaf [⟨decodeRow 12 ("36241075", 8), 567⟩, ⟨decodeRow 12 ("62410735", 6), 568⟩, ⟨decodeRow 12 ("56241037", 6), 567⟩, ⟨decodeRow 12 ("75624130", 8), 566⟩, ⟨decodeRow 12 ("56241370", 8), 567⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("62413750", 8), 568⟩, ⟨decodeRow 12 ("24137560", 6), 569⟩, ⟨decodeRow 12 ("02413765", 8), 568⟩, ⟨decodeRow 12 ("24137605", 8), 569⟩])
                  (.leaf [⟨decodeRow 12 ("41376025", 8), 570⟩, ⟨decodeRow 12 ("13760245", 8), 571⟩, ⟨decodeRow 12 ("37602415", 6), 572⟩, ⟨decodeRow 12 ("53760214", 8), 571⟩, ⟨decodeRow 12 ("37602154", 8), 572⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("76021534", 6), 573⟩, ⟨decodeRow 12 ("47602135", 8), 572⟩, ⟨decodeRow 12 ("76021345", 8), 573⟩, ⟨decodeRow 12 ("60213475", 8), 574⟩, ⟨decodeRow 12 ("02134765", 8), 575⟩])
                  (.leaf [⟨decodeRow 12 ("21347605", 8), 576⟩, ⟨decodeRow 12 ("13476025", 6), 577⟩, ⟨decodeRow 12 ("51347620", 8), 576⟩, ⟨decodeRow 12 ("13476250", 8), 577⟩, ⟨decodeRow 12 ("34762510", 8), 578⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47625130", 6), 579⟩, ⟨decodeRow 12 ("04762531", 8), 578⟩, ⟨decodeRow 12 ("47625301", 8), 579⟩, ⟨decodeRow 12 ("76253041", 8), 580⟩])
                  (.leaf [⟨decodeRow 12 ("62530471", 8), 581⟩, ⟨decodeRow 12 ("25304761", 6), 582⟩, ⟨decodeRow 12 ("12530467", 6), 581⟩, ⟨decodeRow 12 ("71253064", 8), 580⟩, ⟨decodeRow 12 ("12530674", 8), 581⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("25306714", 8), 582⟩, ⟨decodeRow 12 ("53067124", 6), 583⟩, ⟨decodeRow 12 ("45306721", 8), 582⟩, ⟨decodeRow 12 ("53067241", 8), 583⟩, ⟨decodeRow 12 ("30672451", 8), 584⟩])
                  (.leaf [⟨decodeRow 12 ("06724531", 8), 585⟩, ⟨decodeRow 12 ("67245301", 6), 586⟩, ⟨decodeRow 12 ("16724503", 8), 585⟩, ⟨decodeRow 12 ("67245013", 8), 586⟩, ⟨decodeRow 12 ("72450163", 8), 587⟩])))))))))
  (.branch 606
    (.branch 303
      (.branch 151
        (.branch 75
          (.branch 37
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("24501673", 8), 588⟩, ⟨decodeRow 12 ("45016723", 6), 589⟩, ⟨decodeRow 12 ("34501627", 6), 588⟩, ⟨decodeRow 12 ("73450126", 8), 587⟩])
                  (.leaf [⟨decodeRow 12 ("34501276", 8), 588⟩, ⟨decodeRow 12 ("45012736", 8), 589⟩, ⟨decodeRow 12 ("50127346", 8), 590⟩, ⟨decodeRow 12 ("01273456", 6), 591⟩, ⟨decodeRow 12 ("60127354", 8), 590⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("01273564", 8), 591⟩, ⟨decodeRow 12 ("12735604", 6), 592⟩, ⟨decodeRow 12 ("41273506", 8), 591⟩, ⟨decodeRow 12 ("12735046", 8), 592⟩])
                  (.leaf [⟨decodeRow 12 ("27350416", 8), 593⟩, ⟨decodeRow 12 ("73504126", 6), 594⟩, ⟨decodeRow 12 ("67350421", 8), 593⟩, ⟨decodeRow 12 ("73504261", 8), 594⟩, ⟨decodeRow 12 ("35042671", 8), 595⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("50426731", 8), 596⟩, ⟨decodeRow 12 ("04267351", 8), 597⟩, ⟨decodeRow 12 ("42673501", 6), 598⟩, ⟨decodeRow 12 ("14267305", 8), 597⟩])
                  (.leaf [⟨decodeRow 12 ("42673015", 8), 598⟩, ⟨decodeRow 12 ("26730145", 8), 599⟩, ⟨decodeRow 12 ("67301425", 6), 600⟩, ⟨decodeRow 12 ("56730124", 8), 599⟩, ⟨decodeRow 12 ("67301254", 8), 600⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("73012564", 8), 601⟩, ⟨decodeRow 12 ("30125674", 8), 602⟩, ⟨decodeRow 12 ("01256734", 6), 603⟩, ⟨decodeRow 12 ("40125637", 6), 602⟩, ⟨decodeRow 12 ("74012536", 8), 601⟩])
                  (.leaf [⟨decodeRow 12 ("40125376", 8), 602⟩, ⟨decodeRow 12 ("01253746", 8), 603⟩, ⟨decodeRow 12 ("12537406", 8), 604⟩, ⟨decodeRow 12 ("25374016", 6), 605⟩, ⟨decodeRow 12 ("62537410", 8), 604⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("25374160", 8), 605⟩, ⟨decodeRow 12 ("53741620", 8), 606⟩, ⟨decodeRow 12 ("37416250", 6), 607⟩, ⟨decodeRow 12 ("03741652", 8), 606⟩])
                  (.leaf [⟨decodeRow 12 ("37416502", 8), 607⟩, ⟨decodeRow 12 ("74165032", 8), 608⟩, ⟨decodeRow 12 ("41650372", 8), 609⟩, ⟨decodeRow 12 ("16503742", 6), 610⟩, ⟨decodeRow 12 ("21650347", 6), 609⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("72165043", 8), 608⟩, ⟨decodeRow 12 ("21650473", 8), 609⟩, ⟨decodeRow 12 ("16504723", 8), 610⟩, ⟨decodeRow 12 ("65047213", 6), 611⟩, ⟨decodeRow 12 ("36504712", 8), 610⟩])
                  (.leaf [⟨decodeRow 12 ("65047132", 8), 611⟩, ⟨decodeRow 12 ("50471362", 8), 612⟩, ⟨decodeRow 12 ("04713652", 6), 613⟩, ⟨decodeRow 12 ("20471356", 8), 612⟩, ⟨decodeRow 12 ("04713526", 8), 613⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47135206", 8), 614⟩, ⟨decodeRow 12 ("71352046", 8), 615⟩, ⟨decodeRow 12 ("13520476", 8), 616⟩, ⟨decodeRow 12 ("35204716", 6), 617⟩])
                  (.leaf [⟨decodeRow 12 ("63520417", 6), 616⟩, ⟨decodeRow 12 ("76352014", 8), 615⟩, ⟨decodeRow 12 ("63520174", 8), 616⟩, ⟨decodeRow 12 ("35201764", 8), 617⟩, ⟨decodeRow 12 ("52017634", 8), 618⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("20176354", 6), 619⟩, ⟨decodeRow 12 ("42017653", 8), 618⟩, ⟨decodeRow 12 ("20176543", 8), 619⟩, ⟨decodeRow 12 ("01765423", 8), 620⟩, ⟨decodeRow 12 ("17654203", 6), 621⟩])
                  (.leaf [⟨decodeRow 12 ("31765402", 8), 620⟩, ⟨decodeRow 12 ("17654032", 8), 621⟩, ⟨decodeRow 12 ("76540312", 8), 622⟩, ⟨decodeRow 12 ("65403172", 8), 623⟩, ⟨decodeRow 12 ("54031762", 6), 624⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("25403167", 6), 623⟩, ⟨decodeRow 12 ("72540361", 8), 622⟩, ⟨decodeRow 12 ("25403671", 8), 623⟩, ⟨decodeRow 12 ("54036721", 8), 624⟩])
                  (.leaf [⟨decodeRow 12 ("40367251", 6), 625⟩, ⟨decodeRow 12 ("14036752", 8), 624⟩, ⟨decodeRow 12 ("40367512", 8), 625⟩, ⟨decodeRow 12 ("03675142", 8), 626⟩, ⟨decodeRow 12 ("36751402", 8), 627⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("67514032", 6), 628⟩, ⟨decodeRow 12 ("26751430", 8), 627⟩, ⟨decodeRow 12 ("67514320", 8), 628⟩, ⟨decodeRow 12 ("75143260", 8), 629⟩, ⟨decodeRow 12 ("51432670", 8), 630⟩])
                  (.leaf [⟨decodeRow 12 ("14326750", 6), 631⟩, ⟨decodeRow 12 ("01432657", 6), 630⟩, ⟨decodeRow 12 ("70143256", 8), 629⟩, ⟨decodeRow 12 ("01432576", 8), 630⟩, ⟨decodeRow 12 ("14325706", 8), 631⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("43257016", 8), 632⟩, ⟨decodeRow 12 ("32570146", 6), 633⟩, ⟨decodeRow 12 ("63257041", 8), 632⟩, ⟨decodeRow 12 ("32570461", 8), 633⟩])
                  (.leaf [⟨decodeRow 12 ("25704631", 6), 634⟩, ⟨decodeRow 12 ("12570436", 8), 633⟩, ⟨decodeRow 12 ("25704316", 8), 634⟩, ⟨decodeRow 12 ("57043126", 8), 635⟩, ⟨decodeRow 12 ("70431256", 8), 636⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("04312576", 8), 637⟩, ⟨decodeRow 12 ("43125706", 6), 638⟩, ⟨decodeRow 12 ("64312507", 6), 637⟩, ⟨decodeRow 12 ("76431205", 8), 636⟩, ⟨decodeRow 12 ("64312075", 8), 637⟩])
                  (.leaf [⟨decodeRow 12 ("43120765", 8), 638⟩, ⟨decodeRow 12 ("31207645", 8), 639⟩, ⟨decodeRow 12 ("12076435", 6), 640⟩, ⟨decodeRow 12 ("51207634", 8), 639⟩, ⟨decodeRow 12 ("12076354", 8), 640⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("20763514", 8), 641⟩, ⟨decodeRow 12 ("07635124", 6), 642⟩, ⟨decodeRow 12 ("40763521", 8), 641⟩, ⟨decodeRow 12 ("07635241", 8), 642⟩])
                  (.leaf [⟨decodeRow 12 ("76352401", 8), 643⟩, ⟨decodeRow 12 ("63524071", 8), 644⟩, ⟨decodeRow 12 ("35240761", 6), 645⟩, ⟨decodeRow 12 ("13524067", 6), 644⟩, ⟨decodeRow 12 ("71352460", 8), 643⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("13524670", 8), 644⟩, ⟨decodeRow 12 ("35246710", 8), 645⟩, ⟨decodeRow 12 ("52467130", 8), 646⟩, ⟨decodeRow 12 ("24671350", 6), 647⟩, ⟨decodeRow 12 ("02467153", 8), 646⟩])
                  (.leaf [⟨decodeRow 12 ("24671503", 8), 647⟩, ⟨decodeRow 12 ("46715023", 6), 648⟩, ⟨decodeRow 12 ("34671520", 8), 647⟩, ⟨decodeRow 12 ("46715230", 8), 648⟩, ⟨decodeRow 12 ("67152340", 8), 649⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("71523460", 6), 650⟩, ⟨decodeRow 12 ("07152364", 8), 649⟩, ⟨decodeRow 12 ("71523604", 8), 650⟩, ⟨decodeRow 12 ("15236074", 8), 651⟩])
                  (.leaf [⟨decodeRow 12 ("52360714", 8), 652⟩, ⟨decodeRow 12 ("23607154", 8), 653⟩, ⟨decodeRow 12 ("36071524", 6), 654⟩, ⟨decodeRow 12 ("43607125", 8), 653⟩, ⟨decodeRow 12 ("36071245", 8), 654⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("60712435", 8), 655⟩, ⟨decodeRow 12 ("07124365", 6), 656⟩, ⟨decodeRow 12 ("50712463", 8), 655⟩, ⟨decodeRow 12 ("07124653", 8), 656⟩, ⟨decodeRow 12 ("71246503", 8), 657⟩])
                  (.leaf [⟨decodeRow 12 ("12465073", 8), 658⟩, ⟨decodeRow 12 ("24650713", 6), 659⟩, ⟨decodeRow 12 ("32465017", 6), 658⟩, ⟨decodeRow 12 ("73246510", 8), 657⟩, ⟨decodeRow 12 ("32465170", 8), 658⟩]))))))
        (.branch 76
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("24651730", 8), 659⟩, ⟨decodeRow 12 ("46517320", 8), 660⟩, ⟨decodeRow 12 ("65173240", 6), 661⟩, ⟨decodeRow 12 ("06517342", 8), 660⟩])
                  (.leaf [⟨decodeRow 12 ("65173402", 8), 661⟩, ⟨decodeRow 12 ("51734062", 8), 662⟩, ⟨decodeRow 12 ("17340652", 6), 663⟩, ⟨decodeRow 12 ("21734056", 8), 662⟩, ⟨decodeRow 12 ("17340526", 8), 663⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("73405216", 8), 664⟩, ⟨decodeRow 12 ("34052176", 8), 665⟩, ⟨decodeRow 12 ("40521736", 6), 666⟩, ⟨decodeRow 12 ("64052137", 6), 665⟩, ⟨decodeRow 12 ("76405231", 8), 664⟩])
                  (.leaf [⟨decodeRow 12 ("64052371", 8), 665⟩, ⟨decodeRow 12 ("40523761", 8), 666⟩, ⟨decodeRow 12 ("05237641", 6), 667⟩, ⟨decodeRow 12 ("10523746", 8), 666⟩, ⟨decodeRow 12 ("05237416", 8), 667⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("52374106", 8), 668⟩, ⟨decodeRow 12 ("23741056", 6), 669⟩, ⟨decodeRow 12 ("62374150", 8), 668⟩, ⟨decodeRow 12 ("23741560", 8), 669⟩])
                  (.leaf [⟨decodeRow 12 ("37415620", 8), 670⟩, ⟨decodeRow 12 ("74156230", 6), 671⟩, ⟨decodeRow 12 ("07415632", 8), 670⟩, ⟨decodeRow 12 ("74156302", 8), 671⟩, ⟨decodeRow 12 ("41563072", 8), 672⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("15630742", 8), 673⟩, ⟨decodeRow 12 ("56307412", 8), 674⟩, ⟨decodeRow 12 ("63074152", 6), 675⟩, ⟨decodeRow 12 ("26307451", 8), 674⟩, ⟨decodeRow 12 ("63074521", 8), 675⟩])
                  (.leaf [⟨decodeRow 12 ("30745261", 6), 676⟩, ⟨decodeRow 12 ("13074562", 8), 675⟩, ⟨decodeRow 12 ("30745612", 8), 676⟩, ⟨decodeRow 12 ("07456132", 8), 677⟩, ⟨decodeRow 12 ("74561302", 6), 678⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27456103", 8), 677⟩, ⟨decodeRow 12 ("74561023", 8), 678⟩, ⟨decodeRow 12 ("45610273", 8), 679⟩, ⟨decodeRow 12 ("56102743", 8), 680⟩])
                  (.leaf [⟨decodeRow 12 ("61027453", 6), 681⟩, ⟨decodeRow 12 ("36102754", 8), 680⟩, ⟨decodeRow 12 ("61027534", 8), 681⟩, ⟨decodeRow 12 ("10275364", 8), 682⟩, ⟨decodeRow 12 ("02753614", 8), 683⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("27536104", 6), 684⟩, ⟨decodeRow 12 ("42753601", 8), 683⟩, ⟨decodeRow 12 ("27536041", 8), 684⟩, ⟨decodeRow 12 ("75360421", 8), 685⟩, ⟨decodeRow 12 ("53604271", 8), 686⟩])
                  (.leaf [⟨decodeRow 12 ("36042751", 6), 687⟩, ⟨decodeRow 12 ("13604257", 6), 686⟩, ⟨decodeRow 12 ("71360452", 8), 685⟩, ⟨decodeRow 12 ("13604572", 8), 686⟩, ⟨decodeRow 12 ("36045712", 8), 687⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("60457132", 8), 688⟩, ⟨decodeRow 12 ("04571362", 6), 689⟩, ⟨decodeRow 12 ("20457163", 8), 688⟩, ⟨decodeRow 12 ("04571623", 8), 689⟩])
                  (.leaf [⟨decodeRow 12 ("45716203", 8), 690⟩, ⟨decodeRow 12 ("57162043", 6), 691⟩, ⟨decodeRow 12 ("35716240", 8), 690⟩, ⟨decodeRow 12 ("57162430", 8), 691⟩, ⟨decodeRow 12 ("71624350", 8), 692⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("16243570", 8), 693⟩, ⟨decodeRow 12 ("62435710", 6), 694⟩, ⟨decodeRow 12 ("06243517", 6), 693⟩, ⟨decodeRow 12 ("70624315", 8), 692⟩, ⟨decodeRow 12 ("06243175", 8), 693⟩])
                  (.leaf [⟨decodeRow 12 ("62431705", 8), 694⟩, ⟨decodeRow 12 ("24317065", 8), 695⟩, ⟨decodeRow 12 ("43170625", 6), 696⟩, ⟨decodeRow 12 ("54317026", 8), 695⟩, ⟨decodeRow 12 ("43170256", 8), 696⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("31702546", 6), 697⟩, ⟨decodeRow 12 ("63170245", 8), 696⟩, ⟨decodeRow 12 ("31702465", 8), 697⟩, ⟨decodeRow 12 ("17024635", 8), 698⟩])
                  (.leaf [⟨decodeRow 12 ("70246315", 8), 699⟩, ⟨decodeRow 12 ("02463175", 8), 700⟩, ⟨decodeRow 12 ("24631705", 6), 701⟩, ⟨decodeRow 12 ("52463107", 6), 700⟩, ⟨decodeRow 12 ("75246301", 8), 699⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("52463071", 8), 700⟩, ⟨decodeRow 12 ("24630751", 8), 701⟩, ⟨decodeRow 12 ("46307521", 8), 702⟩, ⟨decodeRow 12 ("63075241", 6), 703⟩, ⟨decodeRow 12 ("16307542", 8), 702⟩])
                  (.leaf [⟨decodeRow 12 ("63075412", 8), 703⟩, ⟨decodeRow 12 ("30754162", 8), 704⟩, ⟨decodeRow 12 ("07541632", 6), 705⟩, ⟨decodeRow 12 ("20754136", 8), 704⟩, ⟨decodeRow 12 ("07541326", 8), 705⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("75413206", 8), 706⟩, ⟨decodeRow 12 ("54132076", 8), 707⟩, ⟨decodeRow 12 ("41320756", 6), 708⟩, ⟨decodeRow 12 ("64132057", 6), 707⟩])
                  (.leaf [⟨decodeRow 12 ("76413250", 8), 706⟩, ⟨decodeRow 12 ("64132570", 8), 707⟩, ⟨decodeRow 12 ("41325760", 8), 708⟩, ⟨decodeRow 12 ("13257640", 8), 709⟩, ⟨decodeRow 12 ("32576410", 6), 710⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("03257614", 8), 709⟩, ⟨decodeRow 12 ("32576104", 8), 710⟩, ⟨decodeRow 12 ("25761034", 6), 711⟩, ⟨decodeRow 12 ("42576130", 8), 710⟩, ⟨decodeRow 12 ("25761340", 8), 711⟩])
                  (.leaf [⟨decodeRow 12 ("57613420", 8), 712⟩, ⟨decodeRow 12 ("76134250", 6), 713⟩, ⟨decodeRow 12 ("07613452", 8), 712⟩, ⟨decodeRow 12 ("76134502", 8), 713⟩, ⟨decodeRow 12 ("61345072", 8), 714⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("13450762", 8), 715⟩, ⟨decodeRow 12 ("34507612", 8), 716⟩, ⟨decodeRow 12 ("45076132", 6), 717⟩, ⟨decodeRow 12 ("24507631", 8), 716⟩])
                  (.leaf [⟨decodeRow 12 ("45076321", 8), 717⟩, ⟨decodeRow 12 ("50763241", 8), 718⟩, ⟨decodeRow 12 ("07632451", 6), 719⟩, ⟨decodeRow 12 ("10763254", 8), 718⟩, ⟨decodeRow 12 ("07632514", 8), 719⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("76325104", 8), 720⟩, ⟨decodeRow 12 ("63251074", 8), 721⟩, ⟨decodeRow 12 ("32510764", 6), 722⟩, ⟨decodeRow 12 ("43251067", 6), 721⟩, ⟨decodeRow 12 ("74325160", 8), 720⟩])
                  (.leaf [⟨decodeRow 12 ("43251670", 8), 721⟩, ⟨decodeRow 12 ("32516740", 8), 722⟩, ⟨decodeRow 12 ("25167430", 8), 723⟩, ⟨decodeRow 12 ("51674320", 6), 724⟩, ⟨decodeRow 12 ("05167423", 8), 723⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("51674203", 8), 724⟩, ⟨decodeRow 12 ("16742053", 8), 725⟩, ⟨decodeRow 12 ("67420513", 6), 726⟩, ⟨decodeRow 12 ("36742015", 8), 725⟩])
                  (.leaf [⟨decodeRow 12 ("67420135", 8), 726⟩, ⟨decodeRow 12 ("74201365", 8), 727⟩, ⟨decodeRow 12 ("42013675", 8), 728⟩, ⟨decodeRow 12 ("20136745", 6), 729⟩, ⟨decodeRow 12 ("52013647", 6), 728⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("75201346", 8), 727⟩, ⟨decodeRow 12 ("52013476", 8), 728⟩, ⟨decodeRow 12 ("20134756", 8), 729⟩, ⟨decodeRow 12 ("01347526", 6), 730⟩, ⟨decodeRow 12 ("60134725", 8), 729⟩])
                  (.leaf [⟨decodeRow 12 ("01347265", 8), 730⟩, ⟨decodeRow 12 ("13472605", 8), 731⟩, ⟨decodeRow 12 ("34726015", 6), 732⟩, ⟨decodeRow 12 ("53472610", 8), 731⟩, ⟨decodeRow 12 ("34726150", 8), 732⟩])))))))
      (.branch 151
        (.branch 75
          (.branch 37
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47261530", 8), 733⟩, ⟨decodeRow 12 ("72615340", 8), 734⟩, ⟨decodeRow 12 ("26153470", 8), 735⟩, ⟨decodeRow 12 ("61534720", 6), 736⟩])
                  (.leaf [⟨decodeRow 12 ("06153427", 6), 735⟩, ⟨decodeRow 12 ("70615324", 8), 734⟩, ⟨decodeRow 12 ("06153274", 8), 735⟩, ⟨decodeRow 12 ("61532704", 8), 736⟩, ⟨decodeRow 12 ("15327064", 8), 737⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("53270614", 6), 738⟩, ⟨decodeRow 12 ("45327016", 8), 737⟩, ⟨decodeRow 12 ("53270146", 8), 738⟩, ⟨decodeRow 12 ("32701456", 8), 739⟩])
                  (.leaf [⟨decodeRow 12 ("27014536", 6), 740⟩, ⟨decodeRow 12 ("62701435", 8), 739⟩, ⟨decodeRow 12 ("27014365", 8), 740⟩, ⟨decodeRow 12 ("70143625", 8), 741⟩, ⟨decodeRow 12 ("01436275", 8), 742⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14362705", 6), 743⟩, ⟨decodeRow 12 ("51436207", 6), 742⟩, ⟨decodeRow 12 ("75143602", 8), 741⟩, ⟨decodeRow 12 ("51436072", 8), 742⟩])
                  (.leaf [⟨decodeRow 12 ("14360752", 8), 743⟩, ⟨decodeRow 12 ("43607512", 8), 744⟩, ⟨decodeRow 12 ("36075142", 6), 745⟩, ⟨decodeRow 12 ("23607541", 8), 744⟩, ⟨decodeRow 12 ("36075421", 8), 745⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("60754231", 8), 746⟩, ⟨decodeRow 12 ("07542361", 6), 747⟩, ⟨decodeRow 12 ("10754263", 8), 746⟩, ⟨decodeRow 12 ("07542613", 8), 747⟩, ⟨decodeRow 12 ("75426103", 6), 748⟩])
                  (.leaf [⟨decodeRow 12 ("37542601", 8), 747⟩, ⟨decodeRow 12 ("75426031", 8), 748⟩, ⟨decodeRow 12 ("54260371", 8), 749⟩, ⟨decodeRow 12 ("42603751", 8), 750⟩, ⟨decodeRow 12 ("26037541", 6), 751⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("12603745", 8), 750⟩, ⟨decodeRow 12 ("26037415", 8), 751⟩, ⟨decodeRow 12 ("60374125", 8), 752⟩, ⟨decodeRow 12 ("03741265", 8), 753⟩])
                  (.leaf [⟨decodeRow 12 ("37412605", 6), 754⟩, ⟨decodeRow 12 ("53741206", 8), 753⟩, ⟨decodeRow 12 ("37412056", 8), 754⟩, ⟨decodeRow 12 ("74120536", 8), 755⟩, ⟨decodeRow 12 ("41205376", 8), 756⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("12053746", 6), 757⟩, ⟨decodeRow 12 ("61205347", 6), 756⟩, ⟨decodeRow 12 ("76120543", 8), 755⟩, ⟨decodeRow 12 ("61205473", 8), 756⟩, ⟨decodeRow 12 ("12054763", 8), 757⟩])
                  (.leaf [⟨decodeRow 12 ("20547613", 8), 758⟩, ⟨decodeRow 12 ("05476123", 6), 759⟩, ⟨decodeRow 12 ("30547621", 8), 758⟩, ⟨decodeRow 12 ("05476231", 8), 759⟩, ⟨decodeRow 12 ("54762301", 8), 760⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47623051", 6), 761⟩, ⟨decodeRow 12 ("14762350", 8), 760⟩, ⟨decodeRow 12 ("47623510", 8), 761⟩, ⟨decodeRow 12 ("76235140", 8), 762⟩])
                  (.leaf [⟨decodeRow 12 ("62351470", 8), 763⟩, ⟨decodeRow 12 ("23514760", 6), 764⟩, ⟨decodeRow 12 ("02351467", 6), 763⟩, ⟨decodeRow 12 ("70235164", 8), 762⟩, ⟨decodeRow 12 ("02351674", 8), 763⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("23516704", 8), 764⟩, ⟨decodeRow 12 ("35167024", 8), 765⟩, ⟨decodeRow 12 ("51670234", 6), 766⟩, ⟨decodeRow 12 ("45167032", 8), 765⟩, ⟨decodeRow 12 ("51670342", 8), 766⟩])
                  (.leaf [⟨decodeRow 12 ("16703452", 6), 767⟩, ⟨decodeRow 12 ("21670354", 8), 766⟩, ⟨decodeRow 12 ("16703524", 8), 767⟩, ⟨decodeRow 12 ("67035214", 8), 768⟩, ⟨decodeRow 12 ("70352164", 6), 769⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47035261", 8), 768⟩, ⟨decodeRow 12 ("70352641", 8), 769⟩, ⟨decodeRow 12 ("03526471", 8), 770⟩, ⟨decodeRow 12 ("35264701", 8), 771⟩])
                  (.leaf [⟨decodeRow 12 ("52647031", 8), 772⟩, ⟨decodeRow 12 ("26470351", 6), 773⟩, ⟨decodeRow 12 ("12647053", 8), 772⟩, ⟨decodeRow 12 ("26470513", 8), 773⟩, ⟨decodeRow 12 ("64705123", 8), 774⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("47051263", 6), 775⟩, ⟨decodeRow 12 ("34705162", 8), 774⟩, ⟨decodeRow 12 ("47051632", 8), 775⟩, ⟨decodeRow 12 ("70516342", 8), 776⟩, ⟨decodeRow 12 ("05163472", 8), 777⟩])
                  (.leaf [⟨decodeRow 12 ("51634702", 6), 778⟩, ⟨decodeRow 12 ("25163407", 6), 777⟩, ⟨decodeRow 12 ("72516304", 8), 776⟩, ⟨decodeRow 12 ("25163074", 8), 777⟩, ⟨decodeRow 12 ("51630724", 8), 778⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("16307254", 8), 779⟩, ⟨decodeRow 12 ("63072514", 6), 780⟩, ⟨decodeRow 12 ("46307215", 8), 779⟩, ⟨decodeRow 12 ("63072145", 8), 780⟩])
                  (.leaf [⟨decodeRow 12 ("30721465", 8), 781⟩, ⟨decodeRow 12 ("07214635", 6), 782⟩, ⟨decodeRow 12 ("50721436", 8), 781⟩, ⟨decodeRow 12 ("07214356", 8), 782⟩, ⟨decodeRow 12 ("72143506", 8), 783⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("21435076", 8), 784⟩, ⟨decodeRow 12 ("14350726", 6), 785⟩, ⟨decodeRow 12 ("61435027", 6), 784⟩, ⟨decodeRow 12 ("76143520", 8), 783⟩, ⟨decodeRow 12 ("61435270", 8), 784⟩])
                  (.leaf [⟨decodeRow 12 ("14352760", 8), 785⟩, ⟨decodeRow 12 ("43527610", 6), 786⟩, ⟨decodeRow 12 ("04352716", 8), 785⟩, ⟨decodeRow 12 ("43527106", 8), 786⟩, ⟨decodeRow 12 ("35271046", 8), 787⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("52710436", 6), 788⟩, ⟨decodeRow 12 ("65271034", 8), 787⟩, ⟨decodeRow 12 ("52710364", 8), 788⟩, ⟨decodeRow 12 ("27103654", 8), 789⟩])
                  (.leaf [⟨decodeRow 12 ("71036524", 6), 790⟩, ⟨decodeRow 12 ("47103625", 8), 789⟩, ⟨decodeRow 12 ("71036245", 8), 790⟩, ⟨decodeRow 12 ("10362475", 8), 791⟩, ⟨decodeRow 12 ("03624715", 8), 792⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("36247105", 8), 793⟩, ⟨decodeRow 12 ("62471035", 6), 794⟩, ⟨decodeRow 12 ("56247130", 8), 793⟩, ⟨decodeRow 12 ("62471350", 8), 794⟩, ⟨decodeRow 12 ("24713560", 6), 795⟩])
                  (.leaf [⟨decodeRow 12 ("02471365", 8), 794⟩, ⟨decodeRow 12 ("24713605", 8), 795⟩, ⟨decodeRow 12 ("47136025", 8), 796⟩, ⟨decodeRow 12 ("71360245", 8), 797⟩, ⟨decodeRow 12 ("13602475", 8), 798⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("36024715", 6), 799⟩, ⟨decodeRow 12 ("53602417", 6), 798⟩, ⟨decodeRow 12 ("75360214", 8), 797⟩, ⟨decodeRow 12 ("53602174", 8), 798⟩])
                  (.leaf [⟨decodeRow 12 ("36021754", 8), 799⟩, ⟨decodeRow 12 ("60217534", 6), 800⟩, ⟨decodeRow 12 ("46021735", 8), 799⟩, ⟨decodeRow 12 ("60217345", 8), 800⟩, ⟨decodeRow 12 ("02173465", 8), 801⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("21734605", 8), 802⟩, ⟨decodeRow 12 ("17346025", 6), 803⟩, ⟨decodeRow 12 ("51734620", 8), 802⟩, ⟨decodeRow 12 ("17346250", 8), 803⟩, ⟨decodeRow 12 ("73462510", 8), 804⟩])
                  (.leaf [⟨decodeRow 12 ("34625170", 8), 805⟩, ⟨decodeRow 12 ("46251730", 6), 806⟩, ⟨decodeRow 12 ("04625137", 6), 805⟩, ⟨decodeRow 12 ("70462531", 8), 804⟩, ⟨decodeRow 12 ("04625371", 8), 805⟩]))))))
        (.branch 76
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("46253701", 8), 806⟩, ⟨decodeRow 12 ("62537041", 8), 807⟩, ⟨decodeRow 12 ("25370461", 6), 808⟩, ⟨decodeRow 12 ("12537064", 8), 807⟩])
                  (.leaf [⟨decodeRow 12 ("25370614", 8), 808⟩, ⟨decodeRow 12 ("53706124", 6), 809⟩, ⟨decodeRow 12 ("45370621", 8), 808⟩, ⟨decodeRow 12 ("53706241", 8), 809⟩, ⟨decodeRow 12 ("37062451", 8), 810⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("70624531", 8), 811⟩, ⟨decodeRow 12 ("06245371", 8), 812⟩, ⟨decodeRow 12 ("62453701", 6), 813⟩, ⟨decodeRow 12 ("16245307", 6), 812⟩, ⟨decodeRow 12 ("71624503", 8), 811⟩])
                  (.leaf [⟨decodeRow 12 ("16245073", 8), 812⟩, ⟨decodeRow 12 ("62450713", 8), 813⟩, ⟨decodeRow 12 ("24507163", 8), 814⟩, ⟨decodeRow 12 ("45071623", 6), 815⟩, ⟨decodeRow 12 ("34507126", 8), 814⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45071236", 8), 815⟩, ⟨decodeRow 12 ("50712346", 8), 816⟩, ⟨decodeRow 12 ("07123456", 6), 817⟩, ⟨decodeRow 12 ("60712354", 8), 816⟩])
                  (.leaf [⟨decodeRow 12 ("07123564", 8), 817⟩, ⟨decodeRow 12 ("71235604", 6), 818⟩, ⟨decodeRow 12 ("47123506", 8), 817⟩, ⟨decodeRow 12 ("71235046", 8), 818⟩, ⟨decodeRow 12 ("12350476", 8), 819⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("23504716", 8), 820⟩, ⟨decodeRow 12 ("35047126", 6), 821⟩, ⟨decodeRow 12 ("63504721", 8), 820⟩, ⟨decodeRow 12 ("35047261", 8), 821⟩, ⟨decodeRow 12 ("50472631", 8), 822⟩])
                  (.leaf [⟨decodeRow 12 ("04726351", 8), 823⟩, ⟨decodeRow 12 ("47263501", 6), 824⟩, ⟨decodeRow 12 ("14726305", 8), 823⟩, ⟨decodeRow 12 ("47263015", 8), 824⟩, ⟨decodeRow 12 ("72630145", 8), 825⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("26301475", 8), 826⟩, ⟨decodeRow 12 ("63014725", 6), 827⟩, ⟨decodeRow 12 ("56301427", 6), 826⟩, ⟨decodeRow 12 ("75630124", 8), 825⟩])
                  (.leaf [⟨decodeRow 12 ("56301274", 8), 826⟩, ⟨decodeRow 12 ("63012754", 8), 827⟩, ⟨decodeRow 12 ("30127564", 8), 828⟩, ⟨decodeRow 12 ("01275634", 6), 829⟩, ⟨decodeRow 12 ("40127536", 8), 828⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("01275346", 8), 829⟩, ⟨decodeRow 12 ("12753406", 8), 830⟩, ⟨decodeRow 12 ("27534016", 6), 831⟩, ⟨decodeRow 12 ("62753410", 8), 830⟩, ⟨decodeRow 12 ("27534160", 8), 831⟩])
                  (.leaf [⟨decodeRow 12 ("75341620", 8), 832⟩, ⟨decodeRow 12 ("53416270", 8), 833⟩, ⟨decodeRow 12 ("34162750", 6), 834⟩, ⟨decodeRow 12 ("03416257", 6), 833⟩, ⟨decodeRow 12 ("70341652", 8), 832⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03416572", 8), 833⟩, ⟨decodeRow 12 ("34165702", 8), 834⟩, ⟨decodeRow 12 ("41657032", 8), 835⟩, ⟨decodeRow 12 ("16570342", 6), 836⟩])
                  (.leaf [⟨decodeRow 12 ("21657043", 8), 835⟩, ⟨decodeRow 12 ("16570423", 8), 836⟩, ⟨decodeRow 12 ("65704213", 6), 837⟩, ⟨decodeRow 12 ("36570412", 8), 836⟩, ⟨decodeRow 12 ("65704132", 8), 837⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("57041362", 8), 838⟩, ⟨decodeRow 12 ("70413652", 6), 839⟩, ⟨decodeRow 12 ("27041356", 8), 838⟩, ⟨decodeRow 12 ("70413526", 8), 839⟩, ⟨decodeRow 12 ("04135276", 8), 840⟩])
                  (.leaf [⟨decodeRow 12 ("41352706", 8), 841⟩, ⟨decodeRow 12 ("13527046", 8), 842⟩, ⟨decodeRow 12 ("35270416", 6), 843⟩, ⟨decodeRow 12 ("63527014", 8), 842⟩, ⟨decodeRow 12 ("35270164", 8), 843⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("52701634", 8), 844⟩, ⟨decodeRow 12 ("27016354", 6), 845⟩, ⟨decodeRow 12 ("42701653", 8), 844⟩, ⟨decodeRow 12 ("27016543", 8), 845⟩])
                  (.leaf [⟨decodeRow 12 ("70165423", 8), 846⟩, ⟨decodeRow 12 ("01654273", 8), 847⟩, ⟨decodeRow 12 ("16542703", 6), 848⟩, ⟨decodeRow 12 ("31654207", 6), 847⟩, ⟨decodeRow 12 ("73165402", 8), 846⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("31654072", 8), 847⟩, ⟨decodeRow 12 ("16540732", 8), 848⟩, ⟨decodeRow 12 ("65407312", 8), 849⟩, ⟨decodeRow 12 ("54073162", 6), 850⟩, ⟨decodeRow 12 ("25407361", 8), 849⟩])
                  (.leaf [⟨decodeRow 12 ("54073621", 8), 850⟩, ⟨decodeRow 12 ("40736251", 6), 851⟩, ⟨decodeRow 12 ("14073652", 8), 850⟩, ⟨decodeRow 12 ("40736512", 8), 851⟩, ⟨decodeRow 12 ("07365142", 8), 852⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("73651402", 8), 853⟩, ⟨decodeRow 12 ("36514072", 8), 854⟩, ⟨decodeRow 12 ("65140732", 6), 855⟩, ⟨decodeRow 12 ("26514037", 6), 854⟩])
                  (.leaf [⟨decodeRow 12 ("72651430", 8), 853⟩, ⟨decodeRow 12 ("26514370", 8), 854⟩, ⟨decodeRow 12 ("65143720", 8), 855⟩, ⟨decodeRow 12 ("51437260", 8), 856⟩, ⟨decodeRow 12 ("14372650", 6), 857⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("01437256", 8), 856⟩, ⟨decodeRow 12 ("14372506", 8), 857⟩, ⟨decodeRow 12 ("43725016", 8), 858⟩, ⟨decodeRow 12 ("37250146", 6), 859⟩, ⟨decodeRow 12 ("63725041", 8), 858⟩])
                  (.leaf [⟨decodeRow 12 ("37250461", 8), 859⟩, ⟨decodeRow 12 ("72504631", 8), 860⟩, ⟨decodeRow 12 ("25046371", 8), 861⟩, ⟨decodeRow 12 ("50463721", 6), 862⟩, ⟨decodeRow 12 ("15046327", 6), 861⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("71504623", 8), 860⟩, ⟨decodeRow 12 ("15046273", 8), 861⟩, ⟨decodeRow 12 ("50462713", 8), 862⟩, ⟨decodeRow 12 ("04627153", 8), 863⟩])
                  (.leaf [⟨decodeRow 12 ("46271503", 6), 864⟩, ⟨decodeRow 12 ("34627105", 8), 863⟩, ⟨decodeRow 12 ("46271035", 8), 864⟩, ⟨decodeRow 12 ("62710345", 6), 865⟩, ⟨decodeRow 12 ("56271043", 8), 864⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("62710453", 8), 865⟩, ⟨decodeRow 12 ("27104563", 8), 866⟩, ⟨decodeRow 12 ("71045623", 6), 867⟩, ⟨decodeRow 12 ("37104526", 8), 866⟩, ⟨decodeRow 12 ("71045236", 8), 867⟩])
                  (.leaf [⟨decodeRow 12 ("10452376", 8), 868⟩, ⟨decodeRow 12 ("04523716", 8), 869⟩, ⟨decodeRow 12 ("45237106", 8), 870⟩, ⟨decodeRow 12 ("52371046", 6), 871⟩, ⟨decodeRow 12 ("65237140", 8), 870⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("52371460", 8), 871⟩, ⟨decodeRow 12 ("23714650", 8), 872⟩, ⟨decodeRow 12 ("37146520", 6), 873⟩, ⟨decodeRow 12 ("03714625", 8), 872⟩])
                  (.leaf [⟨decodeRow 12 ("37146205", 8), 873⟩, ⟨decodeRow 12 ("71462035", 8), 874⟩, ⟨decodeRow 12 ("14620375", 8), 875⟩, ⟨decodeRow 12 ("46203715", 6), 876⟩, ⟨decodeRow 12 ("54620317", 6), 875⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("75462013", 8), 874⟩, ⟨decodeRow 12 ("54620173", 8), 875⟩, ⟨decodeRow 12 ("46201753", 8), 876⟩, ⟨decodeRow 12 ("62017543", 8), 877⟩, ⟨decodeRow 12 ("20175463", 6), 878⟩])
                  (.leaf [⟨decodeRow 12 ("32017564", 8), 877⟩, ⟨decodeRow 12 ("20175634", 8), 878⟩, ⟨decodeRow 12 ("01756324", 6), 879⟩, ⟨decodeRow 12 ("40175623", 8), 878⟩, ⟨decodeRow 12 ("01756243", 8), 879⟩]))))))))
    (.branch 303
      (.branch 151
        (.branch 75
          (.branch 37
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("17562403", 8), 880⟩, ⟨decodeRow 12 ("75624013", 8), 881⟩, ⟨decodeRow 12 ("56240173", 8), 882⟩, ⟨decodeRow 12 ("62401753", 6), 883⟩])
                  (.leaf [⟨decodeRow 12 ("36240157", 6), 882⟩, ⟨decodeRow 12 ("73624051", 8), 881⟩, ⟨decodeRow 12 ("36240571", 8), 882⟩, ⟨decodeRow 12 ("62405731", 8), 883⟩, ⟨decodeRow 12 ("24057361", 8), 884⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40573621", 6), 885⟩, ⟨decodeRow 12 ("14057326", 8), 884⟩, ⟨decodeRow 12 ("40573216", 8), 885⟩, ⟨decodeRow 12 ("05732146", 8), 886⟩])
                  (.leaf [⟨decodeRow 12 ("57321406", 6), 887⟩, ⟨decodeRow 12 ("65732104", 8), 886⟩, ⟨decodeRow 12 ("57321064", 8), 887⟩, ⟨decodeRow 12 ("73210654", 8), 888⟩, ⟨decodeRow 12 ("32106574", 8), 889⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("21065734", 6), 890⟩, ⟨decodeRow 12 ("42106537", 6), 889⟩, ⟨decodeRow 12 ("74210635", 8), 888⟩, ⟨decodeRow 12 ("42106375", 8), 889⟩])
                  (.leaf [⟨decodeRow 12 ("21063745", 8), 890⟩, ⟨decodeRow 12 ("10637425", 8), 891⟩, ⟨decodeRow 12 ("06374215", 6), 892⟩, ⟨decodeRow 12 ("50637412", 8), 891⟩, ⟨decodeRow 12 ("06374152", 8), 892⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("63741502", 6), 893⟩, ⟨decodeRow 12 ("26374105", 8), 892⟩, ⟨decodeRow 12 ("63741025", 8), 893⟩, ⟨decodeRow 12 ("37410265", 8), 894⟩, ⟨decodeRow 12 ("74102635", 6), 895⟩])
                  (.leaf [⟨decodeRow 12 ("57410236", 8), 894⟩, ⟨decodeRow 12 ("74102356", 8), 895⟩, ⟨decodeRow 12 ("41023576", 8), 896⟩, ⟨decodeRow 12 ("10235746", 8), 897⟩, ⟨decodeRow 12 ("02357416", 8), 898⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("23574106", 6), 899⟩, ⟨decodeRow 12 ("62357401", 8), 898⟩, ⟨decodeRow 12 ("23574061", 8), 899⟩, ⟨decodeRow 12 ("35740621", 8), 900⟩])
                  (.leaf [⟨decodeRow 12 ("57406231", 6), 901⟩, ⟨decodeRow 12 ("15740632", 8), 900⟩, ⟨decodeRow 12 ("57406312", 8), 901⟩, ⟨decodeRow 12 ("74063152", 8), 902⟩, ⟨decodeRow 12 ("40631572", 8), 903⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("06315742", 6), 904⟩, ⟨decodeRow 12 ("20631547", 6), 903⟩, ⟨decodeRow 12 ("72063145", 8), 902⟩, ⟨decodeRow 12 ("20631475", 8), 903⟩, ⟨decodeRow 12 ("06314725", 8), 904⟩])
                  (.leaf [⟨decodeRow 12 ("63147205", 8), 905⟩, ⟨decodeRow 12 ("31472065", 6), 906⟩, ⟨decodeRow 12 ("53147260", 8), 905⟩, ⟨decodeRow 12 ("31472650", 8), 906⟩, ⟨decodeRow 12 ("14726530", 8), 907⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47265310", 6), 908⟩, ⟨decodeRow 12 ("04726513", 8), 907⟩, ⟨decodeRow 12 ("47265103", 8), 908⟩, ⟨decodeRow 12 ("72651043", 8), 909⟩])
                  (.leaf [⟨decodeRow 12 ("26510473", 8), 910⟩, ⟨decodeRow 12 ("65104723", 6), 911⟩, ⟨decodeRow 12 ("36510427", 6), 910⟩, ⟨decodeRow 12 ("73651024", 8), 909⟩, ⟨decodeRow 12 ("36510274", 8), 910⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("65102734", 8), 911⟩, ⟨decodeRow 12 ("51027364", 6), 912⟩, ⟨decodeRow 12 ("45102763", 8), 911⟩, ⟨decodeRow 12 ("51027643", 8), 912⟩, ⟨decodeRow 12 ("10276453", 8), 913⟩])
                  (.leaf [⟨decodeRow 12 ("02764513", 6), 914⟩, ⟨decodeRow 12 ("30276415", 8), 913⟩, ⟨decodeRow 12 ("02764135", 8), 914⟩, ⟨decodeRow 12 ("27641305", 8), 915⟩, ⟨decodeRow 12 ("76413025", 8), 916⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("64130275", 8), 917⟩, ⟨decodeRow 12 ("41302765", 6), 918⟩, ⟨decodeRow 12 ("54130267", 6), 917⟩, ⟨decodeRow 12 ("75413062", 8), 916⟩])
                  (.leaf [⟨decodeRow 12 ("54130672", 8), 917⟩, ⟨decodeRow 12 ("41306752", 8), 918⟩, ⟨decodeRow 12 ("13067542", 8), 919⟩, ⟨decodeRow 12 ("30675412", 6), 920⟩, ⟨decodeRow 12 ("23067514", 8), 919⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("30675124", 8), 920⟩, ⟨decodeRow 12 ("06751234", 8), 921⟩, ⟨decodeRow 12 ("67512304", 6), 922⟩, ⟨decodeRow 12 ("46751203", 8), 921⟩, ⟨decodeRow 12 ("67512043", 8), 922⟩])
                  (.leaf [⟨decodeRow 12 ("75120463", 8), 923⟩, ⟨decodeRow 12 ("51204673", 8), 924⟩, ⟨decodeRow 12 ("12046753", 6), 925⟩, ⟨decodeRow 12 ("31204657", 6), 924⟩, ⟨decodeRow 12 ("73120456", 8), 923⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("31204576", 8), 924⟩, ⟨decodeRow 12 ("12045736", 8), 925⟩, ⟨decodeRow 12 ("20457316", 8), 926⟩, ⟨decodeRow 12 ("04573126", 6), 927⟩])
                  (.leaf [⟨decodeRow 12 ("60457321", 8), 926⟩, ⟨decodeRow 12 ("04573261", 8), 927⟩, ⟨decodeRow 12 ("45732601", 8), 928⟩, ⟨decodeRow 12 ("57326041", 6), 929⟩, ⟨decodeRow 12 ("15732640", 8), 928⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("57326410", 8), 929⟩, ⟨decodeRow 12 ("73264150", 6), 930⟩, ⟨decodeRow 12 ("07326451", 8), 929⟩, ⟨decodeRow 12 ("73264501", 8), 930⟩, ⟨decodeRow 12 ("32645071", 8), 931⟩])
                  (.leaf [⟨decodeRow 12 ("26450731", 8), 932⟩, ⟨decodeRow 12 ("64507321", 6), 933⟩, ⟨decodeRow 12 ("16450723", 8), 932⟩, ⟨decodeRow 12 ("64507213", 8), 933⟩, ⟨decodeRow 12 ("45072163", 8), 934⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("50721643", 8), 935⟩, ⟨decodeRow 12 ("07216453", 6), 936⟩, ⟨decodeRow 12 ("30721654", 8), 935⟩, ⟨decodeRow 12 ("07216534", 8), 936⟩])
                  (.leaf [⟨decodeRow 12 ("72165304", 8), 937⟩, ⟨decodeRow 12 ("21653074", 8), 938⟩, ⟨decodeRow 12 ("16530724", 6), 939⟩, ⟨decodeRow 12 ("41653027", 6), 938⟩, ⟨decodeRow 12 ("74165320", 8), 937⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("41653270", 8), 938⟩, ⟨decodeRow 12 ("16532740", 8), 939⟩, ⟨decodeRow 12 ("65327410", 8), 940⟩, ⟨decodeRow 12 ("53274160", 6), 941⟩, ⟨decodeRow 12 ("05327461", 8), 940⟩])
                  (.leaf [⟨decodeRow 12 ("53274601", 8), 941⟩, ⟨decodeRow 12 ("32746051", 8), 942⟩, ⟨decodeRow 12 ("27460531", 6), 943⟩, ⟨decodeRow 12 ("12746035", 8), 942⟩, ⟨decodeRow 12 ("27460315", 8), 943⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74603125", 8), 944⟩, ⟨decodeRow 12 ("46031275", 8), 945⟩, ⟨decodeRow 12 ("60312745", 6), 946⟩, ⟨decodeRow 12 ("56031247", 6), 945⟩])
                  (.leaf [⟨decodeRow 12 ("75603142", 8), 944⟩, ⟨decodeRow 12 ("56031472", 8), 945⟩, ⟨decodeRow 12 ("60314752", 8), 946⟩, ⟨decodeRow 12 ("03147562", 8), 947⟩, ⟨decodeRow 12 ("31475602", 6), 948⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("23147506", 8), 947⟩, ⟨decodeRow 12 ("31475026", 8), 948⟩, ⟨decodeRow 12 ("14750236", 6), 949⟩, ⟨decodeRow 12 ("61475032", 8), 948⟩, ⟨decodeRow 12 ("14750362", 8), 949⟩])
                  (.leaf [⟨decodeRow 12 ("47503612", 8), 950⟩, ⟨decodeRow 12 ("75036142", 6), 951⟩, ⟨decodeRow 12 ("27503641", 8), 950⟩, ⟨decodeRow 12 ("75036421", 8), 951⟩, ⟨decodeRow 12 ("50364271", 8), 952⟩]))))))
        (.branch 76
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03642751", 8), 953⟩, ⟨decodeRow 12 ("36427501", 8), 954⟩, ⟨decodeRow 12 ("64275031", 6), 955⟩, ⟨decodeRow 12 ("16427530", 8), 954⟩])
                  (.leaf [⟨decodeRow 12 ("64275310", 8), 955⟩, ⟨decodeRow 12 ("42753160", 8), 956⟩, ⟨decodeRow 12 ("27531640", 6), 957⟩, ⟨decodeRow 12 ("02753146", 8), 956⟩, ⟨decodeRow 12 ("27531406", 8), 957⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("75314026", 8), 958⟩, ⟨decodeRow 12 ("53140276", 8), 959⟩, ⟨decodeRow 12 ("31402756", 6), 960⟩, ⟨decodeRow 12 ("63140257", 6), 959⟩, ⟨decodeRow 12 ("76314052", 8), 958⟩])
                  (.leaf [⟨decodeRow 12 ("63140572", 8), 959⟩, ⟨decodeRow 12 ("31405762", 8), 960⟩, ⟨decodeRow 12 ("14057632", 8), 961⟩, ⟨decodeRow 12 ("40576312", 6), 962⟩, ⟨decodeRow 12 ("24057613", 8), 961⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40576123", 8), 962⟩, ⟨decodeRow 12 ("05761243", 8), 963⟩, ⟨decodeRow 12 ("57612403", 6), 964⟩, ⟨decodeRow 12 ("35761204", 8), 963⟩])
                  (.leaf [⟨decodeRow 12 ("57612034", 8), 964⟩, ⟨decodeRow 12 ("76120354", 8), 965⟩, ⟨decodeRow 12 ("61203574", 8), 966⟩, ⟨decodeRow 12 ("12035764", 6), 967⟩, ⟨decodeRow 12 ("41203567", 6), 966⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("74120365", 8), 965⟩, ⟨decodeRow 12 ("41203675", 8), 966⟩, ⟨decodeRow 12 ("12036745", 8), 967⟩, ⟨decodeRow 12 ("20367415", 6), 968⟩, ⟨decodeRow 12 ("52036714", 8), 967⟩])
                  (.leaf [⟨decodeRow 12 ("20367154", 8), 968⟩, ⟨decodeRow 12 ("03671524", 8), 969⟩, ⟨decodeRow 12 ("36715204", 6), 970⟩, ⟨decodeRow 12 ("43671502", 8), 969⟩, ⟨decodeRow 12 ("36715042", 8), 970⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67150432", 8), 971⟩, ⟨decodeRow 12 ("71504362", 8), 972⟩, ⟨decodeRow 12 ("15043672", 8), 973⟩, ⟨decodeRow 12 ("50436712", 6), 974⟩])
                  (.leaf [⟨decodeRow 12 ("25043617", 6), 973⟩, ⟨decodeRow 12 ("72504316", 8), 972⟩, ⟨decodeRow 12 ("25043176", 8), 973⟩, ⟨decodeRow 12 ("50431726", 8), 974⟩, ⟨decodeRow 12 ("04317256", 8), 975⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("43172506", 6), 976⟩, ⟨decodeRow 12 ("64317205", 8), 975⟩, ⟨decodeRow 12 ("43172065", 8), 976⟩, ⟨decodeRow 12 ("31720645", 8), 977⟩, ⟨decodeRow 12 ("17206435", 6), 978⟩])
                  (.leaf [⟨decodeRow 12 ("51720634", 8), 977⟩, ⟨decodeRow 12 ("17206354", 8), 978⟩, ⟨decodeRow 12 ("72063514", 8), 979⟩, ⟨decodeRow 12 ("20635174", 8), 980⟩, ⟨decodeRow 12 ("06351724", 6), 981⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40635127", 6), 980⟩, ⟨decodeRow 12 ("74063521", 8), 979⟩, ⟨decodeRow 12 ("40635271", 8), 980⟩, ⟨decodeRow 12 ("06352741", 8), 981⟩])
                  (.leaf [⟨decodeRow 12 ("63527401", 8), 982⟩, ⟨decodeRow 12 ("35274061", 6), 983⟩, ⟨decodeRow 12 ("13527460", 8), 982⟩, ⟨decodeRow 12 ("35274610", 8), 983⟩, ⟨decodeRow 12 ("52746130", 8), 984⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("27461350", 6), 985⟩, ⟨decodeRow 12 ("02746153", 8), 984⟩, ⟨decodeRow 12 ("27461503", 8), 985⟩, ⟨decodeRow 12 ("74615023", 6), 986⟩, ⟨decodeRow 12 ("37461520", 8), 985⟩])
                  (.leaf [⟨decodeRow 12 ("74615230", 8), 986⟩, ⟨decodeRow 12 ("46152370", 8), 987⟩, ⟨decodeRow 12 ("61523740", 8), 988⟩, ⟨decodeRow 12 ("15237460", 6), 989⟩, ⟨decodeRow 12 ("01523764", 8), 988⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("15237604", 8), 989⟩, ⟨decodeRow 12 ("52376014", 8), 990⟩, ⟨decodeRow 12 ("23760154", 8), 991⟩, ⟨decodeRow 12 ("37601524", 6), 992⟩])
                  (.leaf [⟨decodeRow 12 ("43760125", 8), 991⟩, ⟨decodeRow 12 ("37601245", 8), 992⟩, ⟨decodeRow 12 ("76012435", 8), 993⟩, ⟨decodeRow 12 ("60124375", 8), 994⟩, ⟨decodeRow 12 ("01243765", 6), 995⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("50124367", 6), 994⟩, ⟨decodeRow 12 ("75012463", 8), 993⟩, ⟨decodeRow 12 ("50124673", 8), 994⟩, ⟨decodeRow 12 ("01246753", 8), 995⟩, ⟨decodeRow 12 ("12467503", 8), 996⟩])
                  (.leaf [⟨decodeRow 12 ("24675013", 6), 997⟩, ⟨decodeRow 12 ("32467510", 8), 996⟩, ⟨decodeRow 12 ("24675130", 8), 997⟩, ⟨decodeRow 12 ("46751320", 8), 998⟩, ⟨decodeRow 12 ("67513240", 6), 999⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("06751342", 8), 998⟩, ⟨decodeRow 12 ("67513402", 8), 999⟩, ⟨decodeRow 12 ("75134062", 8), 1000⟩, ⟨decodeRow 12 ("51340672", 8), 1001⟩])
                  (.leaf [⟨decodeRow 12 ("13406752", 6), 1002⟩, ⟨decodeRow 12 ("21340657", 6), 1001⟩, ⟨decodeRow 12 ("72134056", 8), 1000⟩, ⟨decodeRow 12 ("21340576", 8), 1001⟩, ⟨decodeRow 12 ("13405726", 8), 1002⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("34057216", 8), 1003⟩, ⟨decodeRow 12 ("40572136", 6), 1004⟩, ⟨decodeRow 12 ("64057231", 8), 1003⟩, ⟨decodeRow 12 ("40572361", 8), 1004⟩, ⟨decodeRow 12 ("05723641", 6), 1005⟩])
                  (.leaf [⟨decodeRow 12 ("10572346", 8), 1004⟩, ⟨decodeRow 12 ("05723416", 8), 1005⟩, ⟨decodeRow 12 ("57234106", 8), 1006⟩, ⟨decodeRow 12 ("72341056", 6), 1007⟩, ⟨decodeRow 12 ("67234150", 8), 1006⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("72341560", 8), 1007⟩, ⟨decodeRow 12 ("23415670", 8), 1008⟩, ⟨decodeRow 12 ("34156720", 8), 1009⟩, ⟨decodeRow 12 ("41567230", 6), 1010⟩])
                  (.leaf [⟨decodeRow 12 ("04156732", 8), 1009⟩, ⟨decodeRow 12 ("41567302", 8), 1010⟩, ⟨decodeRow 12 ("15673042", 8), 1011⟩, ⟨decodeRow 12 ("56730412", 8), 1012⟩, ⟨decodeRow 12 ("67304152", 6), 1013⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("26730451", 8), 1012⟩, ⟨decodeRow 12 ("67304521", 8), 1013⟩, ⟨decodeRow 12 ("73045261", 6), 1014⟩, ⟨decodeRow 12 ("17304562", 8), 1013⟩, ⟨decodeRow 12 ("73045612", 8), 1014⟩])
                  (.leaf [⟨decodeRow 12 ("30456172", 8), 1015⟩, ⟨decodeRow 12 ("04561732", 8), 1016⟩, ⟨decodeRow 12 ("45617302", 8), 1017⟩, ⟨decodeRow 12 ("56173042", 6), 1018⟩, ⟨decodeRow 12 ("25617340", 8), 1017⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("56173420", 8), 1018⟩, ⟨decodeRow 12 ("61734250", 6), 1019⟩, ⟨decodeRow 12 ("06173452", 8), 1018⟩, ⟨decodeRow 12 ("61734502", 8), 1019⟩])
                  (.leaf [⟨decodeRow 12 ("17345062", 8), 1020⟩, ⟨decodeRow 12 ("73450612", 8), 1021⟩, ⟨decodeRow 12 ("34506172", 8), 1022⟩, ⟨decodeRow 12 ("45061732", 6), 1023⟩, ⟨decodeRow 12 ("24506137", 6), 1022⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("72450631", 8), 1021⟩, ⟨decodeRow 12 ("24506371", 8), 1022⟩, ⟨decodeRow 12 ("45063721", 8), 1023⟩, ⟨decodeRow 12 ("50637241", 8), 1024⟩, ⟨decodeRow 12 ("06372451", 6), 1025⟩])
                  (.leaf [⟨decodeRow 12 ("10637254", 8), 1024⟩, ⟨decodeRow 12 ("06372514", 8), 1025⟩, ⟨decodeRow 12 ("63725104", 8), 1026⟩, ⟨decodeRow 12 ("37251064", 6), 1027⟩, ⟨decodeRow 12 ("43725160", 8), 1026⟩])))))))
      (.branch 151
        (.branch 75
          (.branch 37
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("37251640", 8), 1027⟩, ⟨decodeRow 12 ("72516430", 8), 1028⟩, ⟨decodeRow 12 ("25164370", 8), 1029⟩, ⟨decodeRow 12 ("51643720", 6), 1030⟩])
                  (.leaf [⟨decodeRow 12 ("05164327", 6), 1029⟩, ⟨decodeRow 12 ("70516423", 8), 1028⟩, ⟨decodeRow 12 ("05164273", 8), 1029⟩, ⟨decodeRow 12 ("51642703", 8), 1030⟩, ⟨decodeRow 12 ("16427053", 8), 1031⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("64270513", 6), 1032⟩, ⟨decodeRow 12 ("36427015", 8), 1031⟩, ⟨decodeRow 12 ("64270135", 8), 1032⟩, ⟨decodeRow 12 ("42701365", 8), 1033⟩])
                  (.leaf [⟨decodeRow 12 ("27013645", 6), 1034⟩, ⟨decodeRow 12 ("52701346", 8), 1033⟩, ⟨decodeRow 12 ("27013456", 8), 1034⟩, ⟨decodeRow 12 ("70134526", 6), 1035⟩, ⟨decodeRow 12 ("67013425", 8), 1034⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("70134265", 8), 1035⟩, ⟨decodeRow 12 ("01342675", 8), 1036⟩, ⟨decodeRow 12 ("13426705", 8), 1037⟩, ⟨decodeRow 12 ("34267015", 6), 1038⟩])
                  (.leaf [⟨decodeRow 12 ("53426710", 8), 1037⟩, ⟨decodeRow 12 ("34267150", 8), 1038⟩, ⟨decodeRow 12 ("42671530", 8), 1039⟩, ⟨decodeRow 12 ("26715340", 6), 1040⟩, ⟨decodeRow 12 ("02671543", 8), 1039⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("26715403", 8), 1040⟩, ⟨decodeRow 12 ("67154023", 8), 1041⟩, ⟨decodeRow 12 ("71540263", 8), 1042⟩, ⟨decodeRow 12 ("15402673", 8), 1043⟩, ⟨decodeRow 12 ("54026713", 6), 1044⟩])
                  (.leaf [⟨decodeRow 12 ("35402617", 6), 1043⟩, ⟨decodeRow 12 ("73540216", 8), 1042⟩, ⟨decodeRow 12 ("35402176", 8), 1043⟩, ⟨decodeRow 12 ("54021736", 8), 1044⟩, ⟨decodeRow 12 ("40217356", 6), 1045⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("64021753", 8), 1044⟩, ⟨decodeRow 12 ("40217563", 8), 1045⟩, ⟨decodeRow 12 ("02175643", 8), 1046⟩, ⟨decodeRow 12 ("21756403", 6), 1047⟩])
                  (.leaf [⟨decodeRow 12 ("32175604", 8), 1046⟩, ⟨decodeRow 12 ("21756034", 8), 1047⟩, ⟨decodeRow 12 ("17560324", 8), 1048⟩, ⟨decodeRow 12 ("75603214", 8), 1049⟩, ⟨decodeRow 12 ("56032174", 8), 1050⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("60321754", 6), 1051⟩, ⟨decodeRow 12 ("46032157", 6), 1050⟩, ⟨decodeRow 12 ("74603251", 8), 1049⟩, ⟨decodeRow 12 ("46032571", 8), 1050⟩, ⟨decodeRow 12 ("60325741", 8), 1051⟩])
                  (.leaf [⟨decodeRow 12 ("03257461", 8), 1052⟩, ⟨decodeRow 12 ("32574601", 6), 1053⟩, ⟨decodeRow 12 ("13257406", 8), 1052⟩, ⟨decodeRow 12 ("32574016", 8), 1053⟩, ⟨decodeRow 12 ("25740136", 8), 1054⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("57401326", 6), 1055⟩, ⟨decodeRow 12 ("65740123", 8), 1054⟩, ⟨decodeRow 12 ("57401263", 8), 1055⟩, ⟨decodeRow 12 ("74012653", 8), 1056⟩])
                  (.leaf [⟨decodeRow 12 ("40126573", 8), 1057⟩, ⟨decodeRow 12 ("01265743", 6), 1058⟩, ⟨decodeRow 12 ("30126547", 6), 1057⟩, ⟨decodeRow 12 ("73012645", 8), 1056⟩, ⟨decodeRow 12 ("30126475", 8), 1057⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("01264735", 8), 1058⟩, ⟨decodeRow 12 ("12647305", 8), 1059⟩, ⟨decodeRow 12 ("26473015", 6), 1060⟩, ⟨decodeRow 12 ("52647310", 8), 1059⟩, ⟨decodeRow 12 ("26473150", 8), 1060⟩])
                  (.leaf [⟨decodeRow 12 ("64731520", 8), 1061⟩, ⟨decodeRow 12 ("47315260", 6), 1062⟩, ⟨decodeRow 12 ("04731562", 8), 1061⟩, ⟨decodeRow 12 ("47315602", 8), 1062⟩, ⟨decodeRow 12 ("73156042", 6), 1063⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27315640", 8), 1062⟩, ⟨decodeRow 12 ("73156420", 8), 1063⟩, ⟨decodeRow 12 ("31564270", 8), 1064⟩, ⟨decodeRow 12 ("15642730", 8), 1065⟩])
                  (.leaf [⟨decodeRow 12 ("56427310", 6), 1066⟩, ⟨decodeRow 12 ("05642713", 8), 1065⟩, ⟨decodeRow 12 ("56427103", 8), 1066⟩, ⟨decodeRow 12 ("64271053", 8), 1067⟩, ⟨decodeRow 12 ("42710563", 8), 1068⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("27105643", 6), 1069⟩, ⟨decodeRow 12 ("32710546", 8), 1068⟩, ⟨decodeRow 12 ("27105436", 8), 1069⟩, ⟨decodeRow 12 ("71054326", 8), 1070⟩, ⟨decodeRow 12 ("10543276", 8), 1071⟩])
                  (.leaf [⟨decodeRow 12 ("05432716", 6), 1072⟩, ⟨decodeRow 12 ("60543217", 6), 1071⟩, ⟨decodeRow 12 ("76054312", 8), 1070⟩, ⟨decodeRow 12 ("60543172", 8), 1071⟩, ⟨decodeRow 12 ("05431762", 8), 1072⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54317602", 8), 1073⟩, ⟨decodeRow 12 ("43176052", 6), 1074⟩, ⟨decodeRow 12 ("24317650", 8), 1073⟩, ⟨decodeRow 12 ("43176520", 8), 1074⟩])
                  (.leaf [⟨decodeRow 12 ("31765240", 8), 1075⟩, ⟨decodeRow 12 ("17652430", 6), 1076⟩, ⟨decodeRow 12 ("01765234", 8), 1075⟩, ⟨decodeRow 12 ("17652304", 8), 1076⟩, ⟨decodeRow 12 ("76523014", 8), 1077⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("65230174", 8), 1078⟩, ⟨decodeRow 12 ("52301764", 6), 1079⟩, ⟨decodeRow 12 ("45230167", 6), 1078⟩, ⟨decodeRow 12 ("74523061", 8), 1077⟩, ⟨decodeRow 12 ("45230671", 8), 1078⟩])
                  (.leaf [⟨decodeRow 12 ("52306741", 8), 1079⟩, ⟨decodeRow 12 ("23067451", 8), 1080⟩, ⟨decodeRow 12 ("30674521", 6), 1081⟩, ⟨decodeRow 12 ("13067425", 8), 1080⟩, ⟨decodeRow 12 ("30674215", 8), 1081⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("06742135", 6), 1082⟩, ⟨decodeRow 12 ("50674231", 8), 1081⟩, ⟨decodeRow 12 ("06742351", 8), 1082⟩, ⟨decodeRow 12 ("67423501", 8), 1083⟩])
                  (.leaf [⟨decodeRow 12 ("74235061", 6), 1084⟩, ⟨decodeRow 12 ("17423560", 8), 1083⟩, ⟨decodeRow 12 ("74235610", 8), 1084⟩, ⟨decodeRow 12 ("42356170", 8), 1085⟩, ⟨decodeRow 12 ("23561740", 8), 1086⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("35617420", 8), 1087⟩, ⟨decodeRow 12 ("56174230", 6), 1088⟩, ⟨decodeRow 12 ("05617432", 8), 1087⟩, ⟨decodeRow 12 ("56174302", 8), 1088⟩, ⟨decodeRow 12 ("61743052", 8), 1089⟩])
                  (.leaf [⟨decodeRow 12 ("17430562", 6), 1090⟩, ⟨decodeRow 12 ("21743065", 8), 1089⟩, ⟨decodeRow 12 ("17430625", 8), 1090⟩, ⟨decodeRow 12 ("74306215", 6), 1091⟩, ⟨decodeRow 12 ("57430612", 8), 1090⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74306152", 8), 1091⟩, ⟨decodeRow 12 ("43061572", 8), 1092⟩, ⟨decodeRow 12 ("30615742", 8), 1093⟩, ⟨decodeRow 12 ("06157432", 6), 1094⟩])
                  (.leaf [⟨decodeRow 12 ("20615734", 8), 1093⟩, ⟨decodeRow 12 ("06157324", 8), 1094⟩, ⟨decodeRow 12 ("61573204", 8), 1095⟩, ⟨decodeRow 12 ("15732064", 8), 1096⟩, ⟨decodeRow 12 ("57320614", 6), 1097⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("45732016", 8), 1096⟩, ⟨decodeRow 12 ("57320146", 8), 1097⟩, ⟨decodeRow 12 ("73201456", 8), 1098⟩, ⟨decodeRow 12 ("32014576", 8), 1099⟩, ⟨decodeRow 12 ("20145736", 6), 1100⟩])
                  (.leaf [⟨decodeRow 12 ("62014537", 6), 1099⟩, ⟨decodeRow 12 ("76201435", 8), 1098⟩, ⟨decodeRow 12 ("62014375", 8), 1099⟩, ⟨decodeRow 12 ("20143765", 8), 1100⟩, ⟨decodeRow 12 ("01437625", 8), 1101⟩]))))))
        (.branch 76
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14376205", 6), 1102⟩, ⟨decodeRow 12 ("51437602", 8), 1101⟩, ⟨decodeRow 12 ("14376052", 8), 1102⟩, ⟨decodeRow 12 ("43760512", 8), 1103⟩])
                  (.leaf [⟨decodeRow 12 ("37605142", 6), 1104⟩, ⟨decodeRow 12 ("23760541", 8), 1103⟩, ⟨decodeRow 12 ("37605421", 8), 1104⟩, ⟨decodeRow 12 ("76054231", 8), 1105⟩, ⟨decodeRow 12 ("60542371", 8), 1106⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("05423761", 6), 1107⟩, ⟨decodeRow 12 ("10542367", 6), 1106⟩, ⟨decodeRow 12 ("71054263", 8), 1105⟩, ⟨decodeRow 12 ("10542673", 8), 1106⟩, ⟨decodeRow 12 ("05426713", 8), 1107⟩])
                  (.leaf [⟨decodeRow 12 ("54267103", 6), 1108⟩, ⟨decodeRow 12 ("35426701", 8), 1107⟩, ⟨decodeRow 12 ("54267031", 8), 1108⟩, ⟨decodeRow 12 ("42670351", 8), 1109⟩, ⟨decodeRow 12 ("26703541", 6), 1110⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("12670345", 8), 1109⟩, ⟨decodeRow 12 ("26703415", 8), 1110⟩, ⟨decodeRow 12 ("67034125", 8), 1111⟩, ⟨decodeRow 12 ("70341265", 8), 1112⟩])
                  (.leaf [⟨decodeRow 12 ("03412675", 8), 1113⟩, ⟨decodeRow 12 ("34126705", 6), 1114⟩, ⟨decodeRow 12 ("53412607", 6), 1113⟩, ⟨decodeRow 12 ("75341206", 8), 1112⟩, ⟨decodeRow 12 ("53412076", 8), 1113⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("34120756", 8), 1114⟩, ⟨decodeRow 12 ("41207536", 8), 1115⟩, ⟨decodeRow 12 ("12075346", 6), 1116⟩, ⟨decodeRow 12 ("61207543", 8), 1115⟩, ⟨decodeRow 12 ("12075463", 8), 1116⟩])
                  (.leaf [⟨decodeRow 12 ("20754613", 8), 1117⟩, ⟨decodeRow 12 ("07546123", 6), 1118⟩, ⟨decodeRow 12 ("30754621", 8), 1117⟩, ⟨decodeRow 12 ("07546231", 8), 1118⟩, ⟨decodeRow 12 ("75462301", 8), 1119⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54623071", 8), 1120⟩, ⟨decodeRow 12 ("46230751", 6), 1121⟩, ⟨decodeRow 12 ("14623057", 6), 1120⟩, ⟨decodeRow 12 ("71462350", 8), 1119⟩])
                  (.leaf [⟨decodeRow 12 ("14623570", 8), 1120⟩, ⟨decodeRow 12 ("46235710", 8), 1121⟩, ⟨decodeRow 12 ("62357140", 8), 1122⟩, ⟨decodeRow 12 ("23571460", 6), 1123⟩, ⟨decodeRow 12 ("02357164", 8), 1122⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("23571604", 8), 1123⟩, ⟨decodeRow 12 ("35716024", 8), 1124⟩, ⟨decodeRow 12 ("57160234", 6), 1125⟩, ⟨decodeRow 12 ("45716032", 8), 1124⟩, ⟨decodeRow 12 ("57160342", 8), 1125⟩])
                  (.leaf [⟨decodeRow 12 ("71603452", 6), 1126⟩, ⟨decodeRow 12 ("27160354", 8), 1125⟩, ⟨decodeRow 12 ("71603524", 8), 1126⟩, ⟨decodeRow 12 ("16035274", 8), 1127⟩, ⟨decodeRow 12 ("60352714", 8), 1128⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03527164", 6), 1129⟩, ⟨decodeRow 12 ("40352761", 8), 1128⟩, ⟨decodeRow 12 ("03527641", 8), 1129⟩, ⟨decodeRow 12 ("35276401", 8), 1130⟩])
                  (.leaf [⟨decodeRow 12 ("52764031", 8), 1131⟩, ⟨decodeRow 12 ("27640351", 6), 1132⟩, ⟨decodeRow 12 ("12764053", 8), 1131⟩, ⟨decodeRow 12 ("27640513", 8), 1132⟩, ⟨decodeRow 12 ("76405123", 8), 1133⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("64051273", 8), 1134⟩, ⟨decodeRow 12 ("40512763", 6), 1135⟩, ⟨decodeRow 12 ("34051267", 6), 1134⟩, ⟨decodeRow 12 ("73405162", 8), 1133⟩, ⟨decodeRow 12 ("34051672", 8), 1134⟩])
                  (.leaf [⟨decodeRow 12 ("40516732", 8), 1135⟩, ⟨decodeRow 12 ("05167342", 8), 1136⟩, ⟨decodeRow 12 ("51673402", 6), 1137⟩, ⟨decodeRow 12 ("25167304", 8), 1136⟩, ⟨decodeRow 12 ("51673024", 8), 1137⟩])))))
          (.branch 38
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("16730254", 8), 1138⟩, ⟨decodeRow 12 ("67302514", 6), 1139⟩, ⟨decodeRow 12 ("46730215", 8), 1138⟩, ⟨decodeRow 12 ("67302145", 8), 1139⟩])
                  (.leaf [⟨decodeRow 12 ("73021465", 8), 1140⟩, ⟨decodeRow 12 ("30214675", 8), 1141⟩, ⟨decodeRow 12 ("02146735", 6), 1142⟩, ⟨decodeRow 12 ("50214637", 6), 1141⟩, ⟨decodeRow 12 ("75021436", 8), 1140⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("50214376", 8), 1141⟩, ⟨decodeRow 12 ("02143756", 8), 1142⟩, ⟨decodeRow 12 ("21437506", 8), 1143⟩, ⟨decodeRow 12 ("14375026", 6), 1144⟩, ⟨decodeRow 12 ("61437520", 8), 1143⟩])
                  (.leaf [⟨decodeRow 12 ("14375260", 8), 1144⟩, ⟨decodeRow 12 ("43752610", 6), 1145⟩, ⟨decodeRow 12 ("04375216", 8), 1144⟩, ⟨decodeRow 12 ("43752106", 8), 1145⟩, ⟨decodeRow 12 ("37521046", 8), 1146⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("75210436", 6), 1147⟩, ⟨decodeRow 12 ("67521034", 8), 1146⟩, ⟨decodeRow 12 ("75210364", 8), 1147⟩, ⟨decodeRow 12 ("52103674", 8), 1148⟩])
                  (.leaf [⟨decodeRow 12 ("21036754", 8), 1149⟩, ⟨decodeRow 12 ("10367524", 6), 1150⟩, ⟨decodeRow 12 ("41036725", 8), 1149⟩, ⟨decodeRow 12 ("10367245", 8), 1150⟩, ⟨decodeRow 12 ("03672415", 8), 1151⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("36724105", 8), 1152⟩, ⟨decodeRow 12 ("67241035", 6), 1153⟩, ⟨decodeRow 12 ("56724130", 8), 1152⟩, ⟨decodeRow 12 ("67241350", 8), 1153⟩, ⟨decodeRow 12 ("72413560", 6), 1154⟩])
                  (.leaf [⟨decodeRow 12 ("07241365", 8), 1153⟩, ⟨decodeRow 12 ("72413605", 8), 1154⟩, ⟨decodeRow 12 ("24136075", 8), 1155⟩, ⟨decodeRow 12 ("41360725", 8), 1156⟩, ⟨decodeRow 12 ("13607245", 8), 1157⟩]))))
            (.branch 19
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("36072415", 6), 1158⟩, ⟨decodeRow 12 ("53607214", 8), 1157⟩, ⟨decodeRow 12 ("36072154", 8), 1158⟩, ⟨decodeRow 12 ("60721534", 6), 1159⟩])
                  (.leaf [⟨decodeRow 12 ("46072135", 8), 1158⟩, ⟨decodeRow 12 ("60721345", 8), 1159⟩, ⟨decodeRow 12 ("07213465", 8), 1160⟩, ⟨decodeRow 12 ("72134605", 8), 1161⟩, ⟨decodeRow 12 ("21346075", 8), 1162⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("13460725", 6), 1163⟩, ⟨decodeRow 12 ("51346027", 6), 1162⟩, ⟨decodeRow 12 ("75134620", 8), 1161⟩, ⟨decodeRow 12 ("51346270", 8), 1162⟩, ⟨decodeRow 12 ("13462750", 8), 1163⟩])
                  (.leaf [⟨decodeRow 12 ("34627510", 8), 1164⟩, ⟨decodeRow 12 ("46275130", 6), 1165⟩, ⟨decodeRow 12 ("04627531", 8), 1164⟩, ⟨decodeRow 12 ("46275301", 8), 1165⟩, ⟨decodeRow 12 ("62753041", 8), 1166⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27530461", 6), 1167⟩, ⟨decodeRow 12 ("12753064", 8), 1166⟩, ⟨decodeRow 12 ("27530614", 8), 1167⟩, ⟨decodeRow 12 ("75306124", 6), 1168⟩])
                  (.leaf [⟨decodeRow 12 ("47530621", 8), 1167⟩, ⟨decodeRow 12 ("75306241", 8), 1168⟩, ⟨decodeRow 12 ("53062471", 8), 1169⟩, ⟨decodeRow 12 ("30624751", 8), 1170⟩, ⟨decodeRow 12 ("06247531", 8), 1171⟩]))
                (.branch 5
                  (.leaf [⟨decodeRow 12 ("62475301", 6), 1172⟩, ⟨decodeRow 12 ("16247503", 8), 1171⟩, ⟨decodeRow 12 ("62475013", 8), 1172⟩, ⟨decodeRow 12 ("24750163", 8), 1173⟩, ⟨decodeRow 12 ("47501623", 6), 1174⟩])
                  (.leaf [⟨decodeRow 12 ("34750126", 8), 1173⟩, ⟨decodeRow 12 ("47501236", 8), 1174⟩, ⟨decodeRow 12 ("75012346", 8), 1175⟩, ⟨decodeRow 12 ("50123476", 8), 1176⟩, ⟨decodeRow 12 ("01234756", 6), 1177⟩])))))))))

theorem rows_eq : tree.flatten.map Point.row = Halfar1.rows := by rfl

theorem excesses_eq : tree.flatten.map Point.excess = Halfar1.prefixes := by rfl

noncomputable def point (i : Nat) : Option Point := tree.get? i

theorem point_sound (i : Nat) {p : Point} (hp : point i = some p) :
    p.Occurs Halfar1.rows :=
  PointTree.get_sound tree Halfar1.rows Halfar1.prefixes rows_eq excesses_eq
    Halfar1.prefixes_checked i hp

end SuperpermutationUpperBound.Native14.Pointers.FastHalfar1
