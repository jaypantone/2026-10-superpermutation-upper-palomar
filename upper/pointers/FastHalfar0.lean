module

public import upper.pointers.PointTree
public import upper.certificate.Halfar0Prefixes

@[expose] public section

/-! Balanced source-point data. Both projections are kernel checked once;
lookup soundness then follows from literal membership in this tree. -/
namespace SuperpermutationUpperBound.Native14.Pointers.FastHalfar0
open Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000

noncomputable def tree : PointTree :=
  .branch 1140
  (.branch 570
    (.branch 285
      (.branch 142
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("70123456", 6), 0⟩, ⟨decodeRow 12 ("67012354", 8), -1⟩, ⟨decodeRow 12 ("70123564", 8), 0⟩, ⟨decodeRow 12 ("01235674", 8), 1⟩, ⟨decodeRow 12 ("12356704", 6), 2⟩, ⟨decodeRow 12 ("41235607", 6), 1⟩, ⟨decodeRow 12 ("74123506", 8), 0⟩, ⟨decodeRow 12 ("41235076", 8), 1⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("12350746", 8), 2⟩, ⟨decodeRow 12 ("23507416", 8), 3⟩, ⟨decodeRow 12 ("35074126", 6), 4⟩, ⟨decodeRow 12 ("63507421", 8), 3⟩])
                  (.leaf [⟨decodeRow 12 ("35074261", 8), 4⟩, ⟨decodeRow 12 ("50742631", 8), 5⟩, ⟨decodeRow 12 ("07426351", 8), 6⟩, ⟨decodeRow 12 ("74263501", 6), 7⟩, ⟨decodeRow 12 ("17426305", 8), 6⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74263015", 8), 7⟩, ⟨decodeRow 12 ("42630175", 8), 8⟩, ⟨decodeRow 12 ("26301745", 8), 9⟩, ⟨decodeRow 12 ("63017425", 6), 10⟩])
                  (.leaf [⟨decodeRow 12 ("56301724", 8), 9⟩, ⟨decodeRow 12 ("63017254", 8), 10⟩, ⟨decodeRow 12 ("30172564", 8), 11⟩, ⟨decodeRow 12 ("01725634", 6), 12⟩, ⟨decodeRow 12 ("40172536", 8), 11⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("01725346", 8), 12⟩, ⟨decodeRow 12 ("17253406", 8), 13⟩, ⟨decodeRow 12 ("72534016", 6), 14⟩, ⟨decodeRow 12 ("67253410", 8), 13⟩])
                  (.leaf [⟨decodeRow 12 ("72534160", 8), 14⟩, ⟨decodeRow 12 ("25341670", 8), 15⟩, ⟨decodeRow 12 ("53416720", 8), 16⟩, ⟨decodeRow 12 ("34167250", 6), 17⟩, ⟨decodeRow 12 ("03416752", 8), 16⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("34167502", 8), 17⟩, ⟨decodeRow 12 ("41675032", 8), 18⟩, ⟨decodeRow 12 ("16750342", 6), 19⟩, ⟨decodeRow 12 ("21675043", 8), 18⟩])
                  (.leaf [⟨decodeRow 12 ("16750423", 8), 19⟩, ⟨decodeRow 12 ("67504213", 6), 20⟩, ⟨decodeRow 12 ("36750412", 8), 19⟩, ⟨decodeRow 12 ("67504132", 8), 20⟩, ⟨decodeRow 12 ("75041362", 8), 21⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("50413672", 8), 22⟩, ⟨decodeRow 12 ("04136752", 6), 23⟩, ⟨decodeRow 12 ("20413657", 6), 22⟩, ⟨decodeRow 12 ("72041356", 8), 21⟩])
                  (.leaf [⟨decodeRow 12 ("20413576", 8), 22⟩, ⟨decodeRow 12 ("04135726", 8), 23⟩, ⟨decodeRow 12 ("41357206", 8), 24⟩, ⟨decodeRow 12 ("13572046", 8), 25⟩, ⟨decodeRow 12 ("35720416", 6), 26⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("63572014", 8), 25⟩, ⟨decodeRow 12 ("35720164", 8), 26⟩, ⟨decodeRow 12 ("57201634", 8), 27⟩, ⟨decodeRow 12 ("72016354", 6), 28⟩])
                  (.leaf [⟨decodeRow 12 ("47201653", 8), 27⟩, ⟨decodeRow 12 ("72016543", 8), 28⟩, ⟨decodeRow 12 ("20165473", 8), 29⟩, ⟨decodeRow 12 ("01654723", 8), 30⟩, ⟨decodeRow 12 ("16547203", 6), 31⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("31654702", 8), 30⟩, ⟨decodeRow 12 ("16547032", 8), 31⟩, ⟨decodeRow 12 ("65470312", 6), 32⟩, ⟨decodeRow 12 ("26547013", 8), 31⟩])
                  (.leaf [⟨decodeRow 12 ("65470123", 8), 32⟩, ⟨decodeRow 12 ("54701263", 8), 33⟩, ⟨decodeRow 12 ("47012653", 8), 34⟩, ⟨decodeRow 12 ("70126543", 6), 35⟩, ⟨decodeRow 12 ("37012645", 8), 34⟩])))))
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("70126435", 8), 35⟩, ⟨decodeRow 12 ("01264375", 8), 36⟩, ⟨decodeRow 12 ("12643705", 8), 37⟩, ⟨decodeRow 12 ("26437015", 6), 38⟩, ⟨decodeRow 12 ("52643710", 8), 37⟩, ⟨decodeRow 12 ("26437150", 8), 38⟩, ⟨decodeRow 12 ("64371520", 8), 39⟩, ⟨decodeRow 12 ("43715260", 6), 40⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("04371562", 8), 39⟩, ⟨decodeRow 12 ("43715602", 8), 40⟩, ⟨decodeRow 12 ("37156042", 6), 41⟩, ⟨decodeRow 12 ("23715640", 8), 40⟩])
                  (.leaf [⟨decodeRow 12 ("37156420", 8), 41⟩, ⟨decodeRow 12 ("71564230", 8), 42⟩, ⟨decodeRow 12 ("15642370", 8), 43⟩, ⟨decodeRow 12 ("56423710", 6), 44⟩, ⟨decodeRow 12 ("05642317", 6), 43⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("70564213", 8), 42⟩, ⟨decodeRow 12 ("05642173", 8), 43⟩, ⟨decodeRow 12 ("56421703", 8), 44⟩, ⟨decodeRow 12 ("64217053", 8), 45⟩])
                  (.leaf [⟨decodeRow 12 ("42170563", 8), 46⟩, ⟨decodeRow 12 ("21705643", 6), 47⟩, ⟨decodeRow 12 ("32170546", 8), 46⟩, ⟨decodeRow 12 ("21705436", 8), 47⟩, ⟨decodeRow 12 ("17054326", 8), 48⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("70543216", 6), 49⟩, ⟨decodeRow 12 ("67054312", 8), 48⟩, ⟨decodeRow 12 ("70543162", 8), 49⟩, ⟨decodeRow 12 ("05431672", 8), 50⟩])
                  (.leaf [⟨decodeRow 12 ("54316702", 8), 51⟩, ⟨decodeRow 12 ("43167052", 6), 52⟩, ⟨decodeRow 12 ("24316750", 8), 51⟩, ⟨decodeRow 12 ("43167520", 8), 52⟩, ⟨decodeRow 12 ("31675240", 8), 53⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("16752430", 6), 54⟩, ⟨decodeRow 12 ("01675234", 8), 53⟩, ⟨decodeRow 12 ("16752304", 8), 54⟩, ⟨decodeRow 12 ("67523014", 8), 55⟩])
                  (.leaf [⟨decodeRow 12 ("75230164", 6), 56⟩, ⟨decodeRow 12 ("47523061", 8), 55⟩, ⟨decodeRow 12 ("75230641", 8), 56⟩, ⟨decodeRow 12 ("52306471", 8), 57⟩, ⟨decodeRow 12 ("23064751", 8), 58⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("30647521", 6), 59⟩, ⟨decodeRow 12 ("13064725", 8), 58⟩, ⟨decodeRow 12 ("30647215", 8), 59⟩, ⟨decodeRow 12 ("06472135", 6), 60⟩])
                  (.leaf [⟨decodeRow 12 ("50647231", 8), 59⟩, ⟨decodeRow 12 ("06472351", 8), 60⟩, ⟨decodeRow 12 ("64723501", 8), 61⟩, ⟨decodeRow 12 ("47235061", 6), 62⟩, ⟨decodeRow 12 ("14723560", 8), 61⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47235610", 8), 62⟩, ⟨decodeRow 12 ("72356140", 8), 63⟩, ⟨decodeRow 12 ("23561470", 8), 64⟩, ⟨decodeRow 12 ("35614720", 8), 65⟩])
                  (.leaf [⟨decodeRow 12 ("56147230", 6), 66⟩, ⟨decodeRow 12 ("05614732", 8), 65⟩, ⟨decodeRow 12 ("56147302", 8), 66⟩, ⟨decodeRow 12 ("61473052", 8), 67⟩, ⟨decodeRow 12 ("14730562", 6), 68⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("21473065", 8), 67⟩, ⟨decodeRow 12 ("14730625", 8), 68⟩, ⟨decodeRow 12 ("47306215", 6), 69⟩, ⟨decodeRow 12 ("54730612", 8), 68⟩])
                  (.leaf [⟨decodeRow 12 ("47306152", 8), 69⟩, ⟨decodeRow 12 ("73061542", 8), 70⟩, ⟨decodeRow 12 ("30615472", 8), 71⟩, ⟨decodeRow 12 ("06154732", 8), 72⟩, ⟨decodeRow 12 ("61547302", 6), 73⟩]))))))
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("26154703", 8), 72⟩, ⟨decodeRow 12 ("61547023", 8), 73⟩, ⟨decodeRow 12 ("15470263", 8), 74⟩, ⟨decodeRow 12 ("54702613", 6), 75⟩, ⟨decodeRow 12 ("35470216", 8), 74⟩, ⟨decodeRow 12 ("54702136", 8), 75⟩, ⟨decodeRow 12 ("47021356", 6), 76⟩, ⟨decodeRow 12 ("64702153", 8), 75⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47021563", 8), 76⟩, ⟨decodeRow 12 ("70215643", 8), 77⟩, ⟨decodeRow 12 ("02156473", 8), 78⟩, ⟨decodeRow 12 ("21564703", 6), 79⟩])
                  (.leaf [⟨decodeRow 12 ("32156407", 6), 78⟩, ⟨decodeRow 12 ("73215604", 8), 77⟩, ⟨decodeRow 12 ("32156074", 8), 78⟩, ⟨decodeRow 12 ("21560734", 8), 79⟩, ⟨decodeRow 12 ("15607324", 8), 80⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("56073214", 8), 81⟩, ⟨decodeRow 12 ("60732154", 6), 82⟩, ⟨decodeRow 12 ("46073251", 8), 81⟩, ⟨decodeRow 12 ("60732541", 8), 82⟩])
                  (.leaf [⟨decodeRow 12 ("07325461", 8), 83⟩, ⟨decodeRow 12 ("73254601", 6), 84⟩, ⟨decodeRow 12 ("17325406", 8), 83⟩, ⟨decodeRow 12 ("73254016", 8), 84⟩, ⟨decodeRow 12 ("32540176", 8), 85⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("25401736", 8), 86⟩, ⟨decodeRow 12 ("54017326", 6), 87⟩, ⟨decodeRow 12 ("65401723", 8), 86⟩, ⟨decodeRow 12 ("54017263", 8), 87⟩])
                  (.leaf [⟨decodeRow 12 ("40172653", 8), 88⟩, ⟨decodeRow 12 ("01726543", 6), 89⟩, ⟨decodeRow 12 ("30172645", 8), 88⟩, ⟨decodeRow 12 ("01726435", 8), 89⟩, ⟨decodeRow 12 ("17264305", 8), 90⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("72643015", 6), 91⟩, ⟨decodeRow 12 ("57264310", 8), 90⟩, ⟨decodeRow 12 ("72643150", 8), 91⟩, ⟨decodeRow 12 ("26431570", 8), 92⟩])
                  (.leaf [⟨decodeRow 12 ("64315720", 8), 93⟩, ⟨decodeRow 12 ("43157260", 6), 94⟩, ⟨decodeRow 12 ("04315762", 8), 93⟩, ⟨decodeRow 12 ("43157602", 8), 94⟩, ⟨decodeRow 12 ("31576042", 6), 95⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("23157640", 8), 94⟩, ⟨decodeRow 12 ("31576420", 8), 95⟩, ⟨decodeRow 12 ("15764230", 8), 96⟩, ⟨decodeRow 12 ("57642310", 6), 97⟩])
                  (.leaf [⟨decodeRow 12 ("05764213", 8), 96⟩, ⟨decodeRow 12 ("57642103", 8), 97⟩, ⟨decodeRow 12 ("76421053", 8), 98⟩, ⟨decodeRow 12 ("64210573", 8), 99⟩, ⟨decodeRow 12 ("42105763", 8), 100⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("21057643", 6), 101⟩, ⟨decodeRow 12 ("32105746", 8), 100⟩, ⟨decodeRow 12 ("21057436", 8), 101⟩, ⟨decodeRow 12 ("10574326", 8), 102⟩])
                  (.leaf [⟨decodeRow 12 ("05743216", 6), 103⟩, ⟨decodeRow 12 ("60574312", 8), 102⟩, ⟨decodeRow 12 ("05743162", 8), 103⟩, ⟨decodeRow 12 ("57431602", 8), 104⟩, ⟨decodeRow 12 ("74316052", 6), 105⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27431650", 8), 104⟩, ⟨decodeRow 12 ("74316520", 8), 105⟩, ⟨decodeRow 12 ("43165270", 8), 106⟩, ⟨decodeRow 12 ("31652740", 8), 107⟩])
                  (.leaf [⟨decodeRow 12 ("16527430", 6), 108⟩, ⟨decodeRow 12 ("01652734", 8), 107⟩, ⟨decodeRow 12 ("16527304", 8), 108⟩, ⟨decodeRow 12 ("65273014", 8), 109⟩, ⟨decodeRow 12 ("52730164", 6), 110⟩])))))
          (.branch 36
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45273061", 8), 109⟩, ⟨decodeRow 12 ("52730641", 8), 110⟩, ⟨decodeRow 12 ("27306451", 8), 111⟩, ⟨decodeRow 12 ("73064521", 6), 112⟩])
                  (.leaf [⟨decodeRow 12 ("17306425", 8), 111⟩, ⟨decodeRow 12 ("73064215", 8), 112⟩, ⟨decodeRow 12 ("30642175", 8), 113⟩, ⟨decodeRow 12 ("06421735", 6), 114⟩, ⟨decodeRow 12 ("50642137", 6), 113⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("75064231", 8), 112⟩, ⟨decodeRow 12 ("50642371", 8), 113⟩, ⟨decodeRow 12 ("06423751", 8), 114⟩, ⟨decodeRow 12 ("64237501", 8), 115⟩])
                  (.leaf [⟨decodeRow 12 ("42375061", 6), 116⟩, ⟨decodeRow 12 ("14237560", 8), 115⟩, ⟨decodeRow 12 ("42375610", 8), 116⟩, ⟨decodeRow 12 ("23756140", 8), 117⟩, ⟨decodeRow 12 ("37561420", 8), 118⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("75614230", 6), 119⟩, ⟨decodeRow 12 ("07561432", 8), 118⟩, ⟨decodeRow 12 ("75614302", 8), 119⟩, ⟨decodeRow 12 ("56143072", 8), 120⟩])
                  (.leaf [⟨decodeRow 12 ("61430752", 8), 121⟩, ⟨decodeRow 12 ("14307562", 6), 122⟩, ⟨decodeRow 12 ("21430765", 8), 121⟩, ⟨decodeRow 12 ("14307625", 8), 122⟩, ⟨decodeRow 12 ("43076215", 6), 123⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54307612", 8), 122⟩, ⟨decodeRow 12 ("43076152", 8), 123⟩, ⟨decodeRow 12 ("30761542", 8), 124⟩, ⟨decodeRow 12 ("07615432", 8), 125⟩])
                  (.leaf [⟨decodeRow 12 ("76154302", 6), 126⟩, ⟨decodeRow 12 ("27615403", 8), 125⟩, ⟨decodeRow 12 ("76154023", 8), 126⟩, ⟨decodeRow 12 ("61540273", 8), 127⟩, ⟨decodeRow 12 ("15402763", 8), 128⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54027613", 6), 129⟩, ⟨decodeRow 12 ("35402716", 8), 128⟩, ⟨decodeRow 12 ("54027136", 8), 129⟩, ⟨decodeRow 12 ("40271356", 6), 130⟩])
                  (.leaf [⟨decodeRow 12 ("64027153", 8), 129⟩, ⟨decodeRow 12 ("40271563", 8), 130⟩, ⟨decodeRow 12 ("02715643", 8), 131⟩, ⟨decodeRow 12 ("27156403", 6), 132⟩, ⟨decodeRow 12 ("32715604", 8), 131⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27156034", 8), 132⟩, ⟨decodeRow 12 ("71560324", 8), 133⟩, ⟨decodeRow 12 ("15603274", 8), 134⟩, ⟨decodeRow 12 ("56032714", 8), 135⟩])
                  (.leaf [⟨decodeRow 12 ("60327154", 6), 136⟩, ⟨decodeRow 12 ("46032751", 8), 135⟩, ⟨decodeRow 12 ("60327541", 8), 136⟩, ⟨decodeRow 12 ("03275461", 8), 137⟩, ⟨decodeRow 12 ("32754601", 6), 138⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("13275406", 8), 137⟩, ⟨decodeRow 12 ("32754016", 8), 138⟩, ⟨decodeRow 12 ("27540136", 8), 139⟩, ⟨decodeRow 12 ("75401326", 6), 140⟩])
                  (.leaf [⟨decodeRow 12 ("67540123", 8), 139⟩, ⟨decodeRow 12 ("75401263", 8), 140⟩, ⟨decodeRow 12 ("54012673", 8), 141⟩, ⟨decodeRow 12 ("40126753", 8), 142⟩, ⟨decodeRow 12 ("01267543", 6), 143⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("30126745", 8), 142⟩, ⟨decodeRow 12 ("01267435", 8), 143⟩, ⟨decodeRow 12 ("12674305", 8), 144⟩, ⟨decodeRow 12 ("26743015", 6), 145⟩])
                  (.leaf [⟨decodeRow 12 ("52674310", 8), 144⟩, ⟨decodeRow 12 ("26743150", 8), 145⟩, ⟨decodeRow 12 ("67431520", 8), 146⟩, ⟨decodeRow 12 ("74315260", 6), 147⟩, ⟨decodeRow 12 ("07431562", 8), 146⟩])))))))
      (.branch 142
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("74315602", 8), 147⟩, ⟨decodeRow 12 ("43156072", 8), 148⟩, ⟨decodeRow 12 ("31560742", 6), 149⟩, ⟨decodeRow 12 ("23156047", 6), 148⟩, ⟨decodeRow 12 ("72315640", 8), 147⟩, ⟨decodeRow 12 ("23156470", 8), 148⟩, ⟨decodeRow 12 ("31564720", 8), 149⟩, ⟨decodeRow 12 ("15647230", 8), 150⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("56472310", 6), 151⟩, ⟨decodeRow 12 ("05647213", 8), 150⟩, ⟨decodeRow 12 ("56472103", 8), 151⟩, ⟨decodeRow 12 ("64721053", 8), 152⟩])
                  (.leaf [⟨decodeRow 12 ("47210563", 8), 153⟩, ⟨decodeRow 12 ("72105643", 6), 154⟩, ⟨decodeRow 12 ("37210546", 8), 153⟩, ⟨decodeRow 12 ("72105436", 8), 154⟩, ⟨decodeRow 12 ("21054376", 8), 155⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("10543726", 8), 156⟩, ⟨decodeRow 12 ("05437216", 6), 157⟩, ⟨decodeRow 12 ("60543712", 8), 156⟩, ⟨decodeRow 12 ("05437162", 8), 157⟩])
                  (.leaf [⟨decodeRow 12 ("54371602", 8), 158⟩, ⟨decodeRow 12 ("43716052", 6), 159⟩, ⟨decodeRow 12 ("24371650", 8), 158⟩, ⟨decodeRow 12 ("43716520", 8), 159⟩, ⟨decodeRow 12 ("37165240", 8), 160⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("71652430", 6), 161⟩, ⟨decodeRow 12 ("07165234", 8), 160⟩, ⟨decodeRow 12 ("71652304", 8), 161⟩, ⟨decodeRow 12 ("16523074", 8), 162⟩])
                  (.leaf [⟨decodeRow 12 ("65230714", 8), 163⟩, ⟨decodeRow 12 ("52307164", 6), 164⟩, ⟨decodeRow 12 ("45230761", 8), 163⟩, ⟨decodeRow 12 ("52307641", 8), 164⟩, ⟨decodeRow 12 ("23076451", 8), 165⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("30764521", 6), 166⟩, ⟨decodeRow 12 ("13076425", 8), 165⟩, ⟨decodeRow 12 ("30764215", 8), 166⟩, ⟨decodeRow 12 ("07642135", 6), 167⟩])
                  (.leaf [⟨decodeRow 12 ("50764231", 8), 166⟩, ⟨decodeRow 12 ("07642351", 8), 167⟩, ⟨decodeRow 12 ("76423501", 8), 168⟩, ⟨decodeRow 12 ("64235071", 8), 169⟩, ⟨decodeRow 12 ("42350761", 6), 170⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14235067", 6), 169⟩, ⟨decodeRow 12 ("71423560", 8), 168⟩, ⟨decodeRow 12 ("14235670", 8), 169⟩, ⟨decodeRow 12 ("42356710", 8), 170⟩])
                  (.leaf [⟨decodeRow 12 ("23567140", 8), 171⟩, ⟨decodeRow 12 ("35671420", 8), 172⟩, ⟨decodeRow 12 ("56714230", 6), 173⟩, ⟨decodeRow 12 ("05671432", 8), 172⟩, ⟨decodeRow 12 ("56714302", 8), 173⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67143052", 8), 174⟩, ⟨decodeRow 12 ("71430562", 6), 175⟩, ⟨decodeRow 12 ("27143065", 8), 174⟩, ⟨decodeRow 12 ("71430625", 8), 175⟩])
                  (.leaf [⟨decodeRow 12 ("14306275", 8), 176⟩, ⟨decodeRow 12 ("43062715", 6), 177⟩, ⟨decodeRow 12 ("54306217", 6), 176⟩, ⟨decodeRow 12 ("75430612", 8), 175⟩, ⟨decodeRow 12 ("54306172", 8), 176⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("43061752", 8), 177⟩, ⟨decodeRow 12 ("30617542", 8), 178⟩, ⟨decodeRow 12 ("06175432", 8), 179⟩, ⟨decodeRow 12 ("61754302", 6), 180⟩])
                  (.leaf [⟨decodeRow 12 ("26175403", 8), 179⟩, ⟨decodeRow 12 ("61754023", 8), 180⟩, ⟨decodeRow 12 ("17540263", 8), 181⟩, ⟨decodeRow 12 ("75402613", 6), 182⟩, ⟨decodeRow 12 ("37540216", 8), 181⟩])))))
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("75402136", 8), 182⟩, ⟨decodeRow 12 ("54021376", 8), 183⟩, ⟨decodeRow 12 ("40213756", 6), 184⟩, ⟨decodeRow 12 ("64021357", 6), 183⟩, ⟨decodeRow 12 ("76402153", 8), 182⟩, ⟨decodeRow 12 ("64021573", 8), 183⟩, ⟨decodeRow 12 ("40215763", 8), 184⟩, ⟨decodeRow 12 ("02157643", 8), 185⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("21576403", 6), 186⟩, ⟨decodeRow 12 ("32157604", 8), 185⟩, ⟨decodeRow 12 ("21576034", 8), 186⟩, ⟨decodeRow 12 ("15760324", 8), 187⟩])
                  (.leaf [⟨decodeRow 12 ("57603214", 8), 188⟩, ⟨decodeRow 12 ("76032154", 6), 189⟩, ⟨decodeRow 12 ("47603251", 8), 188⟩, ⟨decodeRow 12 ("76032541", 8), 189⟩, ⟨decodeRow 12 ("60325471", 8), 190⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03254761", 8), 191⟩, ⟨decodeRow 12 ("32547601", 6), 192⟩, ⟨decodeRow 12 ("13254706", 8), 191⟩, ⟨decodeRow 12 ("32547016", 8), 192⟩])
                  (.leaf [⟨decodeRow 12 ("25470136", 6), 193⟩, ⟨decodeRow 12 ("62547031", 8), 192⟩, ⟨decodeRow 12 ("25470361", 8), 193⟩, ⟨decodeRow 12 ("54703621", 8), 194⟩, ⟨decodeRow 12 ("47036251", 6), 195⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14703652", 8), 194⟩, ⟨decodeRow 12 ("47036512", 8), 195⟩, ⟨decodeRow 12 ("70365142", 8), 196⟩, ⟨decodeRow 12 ("03651472", 8), 197⟩])
                  (.leaf [⟨decodeRow 12 ("36514702", 8), 198⟩, ⟨decodeRow 12 ("65147032", 6), 199⟩, ⟨decodeRow 12 ("26514730", 8), 198⟩, ⟨decodeRow 12 ("65147320", 8), 199⟩, ⟨decodeRow 12 ("51473260", 8), 200⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14732650", 6), 201⟩, ⟨decodeRow 12 ("01473256", 8), 200⟩, ⟨decodeRow 12 ("14732506", 8), 201⟩, ⟨decodeRow 12 ("47325016", 8), 202⟩])
                  (.leaf [⟨decodeRow 12 ("73250146", 6), 203⟩, ⟨decodeRow 12 ("67325041", 8), 202⟩, ⟨decodeRow 12 ("73250461", 8), 203⟩, ⟨decodeRow 12 ("32504671", 8), 204⟩, ⟨decodeRow 12 ("25046731", 8), 205⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("50467321", 6), 206⟩, ⟨decodeRow 12 ("15046723", 8), 205⟩, ⟨decodeRow 12 ("50467213", 8), 206⟩, ⟨decodeRow 12 ("04672153", 8), 207⟩])
                  (.leaf [⟨decodeRow 12 ("46721503", 6), 208⟩, ⟨decodeRow 12 ("34672105", 8), 207⟩, ⟨decodeRow 12 ("46721035", 8), 208⟩, ⟨decodeRow 12 ("67210345", 6), 209⟩, ⟨decodeRow 12 ("56721043", 8), 208⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67210453", 8), 209⟩, ⟨decodeRow 12 ("72104563", 8), 210⟩, ⟨decodeRow 12 ("21045673", 8), 211⟩, ⟨decodeRow 12 ("10456723", 6), 212⟩])
                  (.leaf [⟨decodeRow 12 ("31045627", 6), 211⟩, ⟨decodeRow 12 ("73104526", 8), 210⟩, ⟨decodeRow 12 ("31045276", 8), 211⟩, ⟨decodeRow 12 ("10452736", 8), 212⟩, ⟨decodeRow 12 ("04527316", 8), 213⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45273106", 8), 214⟩, ⟨decodeRow 12 ("52731046", 6), 215⟩, ⟨decodeRow 12 ("65273140", 8), 214⟩, ⟨decodeRow 12 ("52731460", 8), 215⟩])
                  (.leaf [⟨decodeRow 12 ("27314650", 8), 216⟩, ⟨decodeRow 12 ("73146520", 6), 217⟩, ⟨decodeRow 12 ("07314625", 8), 216⟩, ⟨decodeRow 12 ("73146205", 8), 217⟩, ⟨decodeRow 12 ("31462075", 8), 218⟩]))))))
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("14620735", 8), 219⟩, ⟨decodeRow 12 ("46207315", 6), 220⟩, ⟨decodeRow 12 ("54620713", 8), 219⟩, ⟨decodeRow 12 ("46207153", 8), 220⟩, ⟨decodeRow 12 ("62071543", 8), 221⟩, ⟨decodeRow 12 ("20715463", 6), 222⟩, ⟨decodeRow 12 ("32071564", 8), 221⟩, ⟨decodeRow 12 ("20715634", 8), 222⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("07156324", 6), 223⟩, ⟨decodeRow 12 ("40715623", 8), 222⟩, ⟨decodeRow 12 ("07156243", 8), 223⟩, ⟨decodeRow 12 ("71562403", 8), 224⟩])
                  (.leaf [⟨decodeRow 12 ("15624073", 8), 225⟩, ⟨decodeRow 12 ("56240713", 8), 226⟩, ⟨decodeRow 12 ("62407153", 6), 227⟩, ⟨decodeRow 12 ("36240751", 8), 226⟩, ⟨decodeRow 12 ("62407531", 8), 227⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("24075361", 8), 228⟩, ⟨decodeRow 12 ("40753621", 6), 229⟩, ⟨decodeRow 12 ("14075326", 8), 228⟩, ⟨decodeRow 12 ("40753216", 8), 229⟩])
                  (.leaf [⟨decodeRow 12 ("07532146", 8), 230⟩, ⟨decodeRow 12 ("75321406", 6), 231⟩, ⟨decodeRow 12 ("67532104", 8), 230⟩, ⟨decodeRow 12 ("75321064", 8), 231⟩, ⟨decodeRow 12 ("53210674", 8), 232⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("32106754", 8), 233⟩, ⟨decodeRow 12 ("21067534", 6), 234⟩, ⟨decodeRow 12 ("42106735", 8), 233⟩, ⟨decodeRow 12 ("21067345", 8), 234⟩])
                  (.leaf [⟨decodeRow 12 ("10673425", 8), 235⟩, ⟨decodeRow 12 ("06734215", 6), 236⟩, ⟨decodeRow 12 ("50673412", 8), 235⟩, ⟨decodeRow 12 ("06734152", 8), 236⟩, ⟨decodeRow 12 ("67341502", 6), 237⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("26734105", 8), 236⟩, ⟨decodeRow 12 ("67341025", 8), 237⟩, ⟨decodeRow 12 ("73410265", 8), 238⟩, ⟨decodeRow 12 ("34102675", 8), 239⟩])
                  (.leaf [⟨decodeRow 12 ("41026735", 6), 240⟩, ⟨decodeRow 12 ("54102637", 6), 239⟩, ⟨decodeRow 12 ("75410236", 8), 238⟩, ⟨decodeRow 12 ("54102376", 8), 239⟩, ⟨decodeRow 12 ("41023756", 8), 240⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("10237546", 8), 241⟩, ⟨decodeRow 12 ("02375416", 8), 242⟩, ⟨decodeRow 12 ("23754106", 6), 243⟩, ⟨decodeRow 12 ("62375401", 8), 242⟩])
                  (.leaf [⟨decodeRow 12 ("23754061", 8), 243⟩, ⟨decodeRow 12 ("37540621", 8), 244⟩, ⟨decodeRow 12 ("75406231", 6), 245⟩, ⟨decodeRow 12 ("17540632", 8), 244⟩, ⟨decodeRow 12 ("75406312", 8), 245⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54063172", 8), 246⟩, ⟨decodeRow 12 ("40631752", 8), 247⟩, ⟨decodeRow 12 ("06317542", 6), 248⟩, ⟨decodeRow 12 ("20631745", 8), 247⟩])
                  (.leaf [⟨decodeRow 12 ("06317425", 8), 248⟩, ⟨decodeRow 12 ("63174205", 8), 249⟩, ⟨decodeRow 12 ("31742065", 6), 250⟩, ⟨decodeRow 12 ("53174260", 8), 249⟩, ⟨decodeRow 12 ("31742650", 8), 250⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("17426530", 8), 251⟩, ⟨decodeRow 12 ("74265310", 6), 252⟩, ⟨decodeRow 12 ("07426513", 8), 251⟩, ⟨decodeRow 12 ("74265103", 8), 252⟩])
                  (.leaf [⟨decodeRow 12 ("42651073", 8), 253⟩, ⟨decodeRow 12 ("26510743", 8), 254⟩, ⟨decodeRow 12 ("65107423", 6), 255⟩, ⟨decodeRow 12 ("36510724", 8), 254⟩, ⟨decodeRow 12 ("65107234", 8), 255⟩])))))
          (.branch 36
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("51072364", 6), 256⟩, ⟨decodeRow 12 ("45107263", 8), 255⟩, ⟨decodeRow 12 ("51072643", 8), 256⟩, ⟨decodeRow 12 ("10726453", 8), 257⟩])
                  (.leaf [⟨decodeRow 12 ("07264513", 6), 258⟩, ⟨decodeRow 12 ("30726415", 8), 257⟩, ⟨decodeRow 12 ("07264135", 8), 258⟩, ⟨decodeRow 12 ("72641305", 8), 259⟩, ⟨decodeRow 12 ("26413075", 8), 260⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("64130725", 8), 261⟩, ⟨decodeRow 12 ("41307265", 6), 262⟩, ⟨decodeRow 12 ("54130762", 8), 261⟩, ⟨decodeRow 12 ("41307652", 8), 262⟩])
                  (.leaf [⟨decodeRow 12 ("13076542", 8), 263⟩, ⟨decodeRow 12 ("30765412", 6), 264⟩, ⟨decodeRow 12 ("23076514", 8), 263⟩, ⟨decodeRow 12 ("30765124", 8), 264⟩, ⟨decodeRow 12 ("07651234", 8), 265⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76512304", 6), 266⟩, ⟨decodeRow 12 ("47651203", 8), 265⟩, ⟨decodeRow 12 ("76512043", 8), 266⟩, ⟨decodeRow 12 ("65120473", 8), 267⟩])
                  (.leaf [⟨decodeRow 12 ("51204763", 8), 268⟩, ⟨decodeRow 12 ("12047653", 6), 269⟩, ⟨decodeRow 12 ("31204756", 8), 268⟩, ⟨decodeRow 12 ("12047536", 8), 269⟩, ⟨decodeRow 12 ("20475316", 8), 270⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("04753126", 6), 271⟩, ⟨decodeRow 12 ("60475321", 8), 270⟩, ⟨decodeRow 12 ("04753261", 8), 271⟩, ⟨decodeRow 12 ("47532601", 8), 272⟩])
                  (.leaf [⟨decodeRow 12 ("75326041", 6), 273⟩, ⟨decodeRow 12 ("17532640", 8), 272⟩, ⟨decodeRow 12 ("75326410", 8), 273⟩, ⟨decodeRow 12 ("53264170", 8), 274⟩, ⟨decodeRow 12 ("32641750", 6), 275⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03264157", 6), 274⟩, ⟨decodeRow 12 ("70326451", 8), 273⟩, ⟨decodeRow 12 ("03264571", 8), 274⟩, ⟨decodeRow 12 ("32645701", 8), 275⟩])
                  (.leaf [⟨decodeRow 12 ("26457031", 8), 276⟩, ⟨decodeRow 12 ("64570321", 6), 277⟩, ⟨decodeRow 12 ("16457023", 8), 276⟩, ⟨decodeRow 12 ("64570213", 8), 277⟩, ⟨decodeRow 12 ("45702163", 8), 278⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("57021643", 8), 279⟩, ⟨decodeRow 12 ("70216453", 6), 280⟩, ⟨decodeRow 12 ("37021654", 8), 279⟩, ⟨decodeRow 12 ("70216534", 8), 280⟩])
                  (.leaf [⟨decodeRow 12 ("02165374", 8), 281⟩, ⟨decodeRow 12 ("21653704", 8), 282⟩, ⟨decodeRow 12 ("16537024", 6), 283⟩, ⟨decodeRow 12 ("41653720", 8), 282⟩, ⟨decodeRow 12 ("16537240", 8), 283⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("65372410", 8), 284⟩, ⟨decodeRow 12 ("53724160", 6), 285⟩, ⟨decodeRow 12 ("05372461", 8), 284⟩, ⟨decodeRow 12 ("53724601", 8), 285⟩])
                  (.leaf [⟨decodeRow 12 ("37246051", 8), 286⟩, ⟨decodeRow 12 ("72460531", 6), 287⟩, ⟨decodeRow 12 ("17246035", 8), 286⟩, ⟨decodeRow 12 ("72460315", 8), 287⟩, ⟨decodeRow 12 ("24603175", 8), 288⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("46031725", 8), 289⟩, ⟨decodeRow 12 ("60317245", 6), 290⟩, ⟨decodeRow 12 ("56031742", 8), 289⟩, ⟨decodeRow 12 ("60317452", 8), 290⟩])
                  (.leaf [⟨decodeRow 12 ("03174562", 8), 291⟩, ⟨decodeRow 12 ("31745602", 6), 292⟩, ⟨decodeRow 12 ("23174506", 8), 291⟩, ⟨decodeRow 12 ("31745026", 8), 292⟩, ⟨decodeRow 12 ("17450236", 6), 293⟩]))))))))
    (.branch 285
      (.branch 142
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("61745032", 8), 292⟩, ⟨decodeRow 12 ("17450362", 8), 293⟩, ⟨decodeRow 12 ("74503612", 8), 294⟩, ⟨decodeRow 12 ("45036172", 8), 295⟩, ⟨decodeRow 12 ("50361742", 6), 296⟩, ⟨decodeRow 12 ("25036147", 6), 295⟩, ⟨decodeRow 12 ("72503641", 8), 294⟩, ⟨decodeRow 12 ("25036471", 8), 295⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("50364721", 8), 296⟩, ⟨decodeRow 12 ("03647251", 8), 297⟩, ⟨decodeRow 12 ("36472501", 8), 298⟩, ⟨decodeRow 12 ("64725031", 6), 299⟩])
                  (.leaf [⟨decodeRow 12 ("16472530", 8), 298⟩, ⟨decodeRow 12 ("64725310", 8), 299⟩, ⟨decodeRow 12 ("47253160", 8), 300⟩, ⟨decodeRow 12 ("72531640", 6), 301⟩, ⟨decodeRow 12 ("07253146", 8), 300⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("72531406", 8), 301⟩, ⟨decodeRow 12 ("25314076", 8), 302⟩, ⟨decodeRow 12 ("53140726", 8), 303⟩, ⟨decodeRow 12 ("31407256", 6), 304⟩])
                  (.leaf [⟨decodeRow 12 ("63140752", 8), 303⟩, ⟨decodeRow 12 ("31407562", 8), 304⟩, ⟨decodeRow 12 ("14075632", 8), 305⟩, ⟨decodeRow 12 ("40756312", 6), 306⟩, ⟨decodeRow 12 ("24075613", 8), 305⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40756123", 8), 306⟩, ⟨decodeRow 12 ("07561243", 8), 307⟩, ⟨decodeRow 12 ("75612403", 6), 308⟩, ⟨decodeRow 12 ("37561204", 8), 307⟩])
                  (.leaf [⟨decodeRow 12 ("75612034", 8), 308⟩, ⟨decodeRow 12 ("56120374", 8), 309⟩, ⟨decodeRow 12 ("61203754", 8), 310⟩, ⟨decodeRow 12 ("12037564", 6), 311⟩, ⟨decodeRow 12 ("41203765", 8), 310⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("12037645", 8), 311⟩, ⟨decodeRow 12 ("20376415", 6), 312⟩, ⟨decodeRow 12 ("52037614", 8), 311⟩, ⟨decodeRow 12 ("20376154", 8), 312⟩])
                  (.leaf [⟨decodeRow 12 ("03761524", 8), 313⟩, ⟨decodeRow 12 ("37615204", 6), 314⟩, ⟨decodeRow 12 ("43761502", 8), 313⟩, ⟨decodeRow 12 ("37615042", 8), 314⟩, ⟨decodeRow 12 ("76150432", 8), 315⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("61504372", 8), 316⟩, ⟨decodeRow 12 ("15043762", 8), 317⟩, ⟨decodeRow 12 ("50437612", 6), 318⟩, ⟨decodeRow 12 ("25043716", 8), 317⟩])
                  (.leaf [⟨decodeRow 12 ("50437126", 8), 318⟩, ⟨decodeRow 12 ("04371256", 8), 319⟩, ⟨decodeRow 12 ("43712506", 6), 320⟩, ⟨decodeRow 12 ("64371205", 8), 319⟩, ⟨decodeRow 12 ("43712065", 8), 320⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("37120645", 8), 321⟩, ⟨decodeRow 12 ("71206435", 6), 322⟩, ⟨decodeRow 12 ("57120634", 8), 321⟩, ⟨decodeRow 12 ("71206354", 8), 322⟩])
                  (.leaf [⟨decodeRow 12 ("12063574", 8), 323⟩, ⟨decodeRow 12 ("20635714", 8), 324⟩, ⟨decodeRow 12 ("06357124", 6), 325⟩, ⟨decodeRow 12 ("40635721", 8), 324⟩, ⟨decodeRow 12 ("06357241", 8), 325⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("63572401", 8), 326⟩, ⟨decodeRow 12 ("35724061", 6), 327⟩, ⟨decodeRow 12 ("13572460", 8), 326⟩, ⟨decodeRow 12 ("35724610", 8), 327⟩])
                  (.leaf [⟨decodeRow 12 ("57246130", 8), 328⟩, ⟨decodeRow 12 ("72461350", 6), 329⟩, ⟨decodeRow 12 ("07246153", 8), 328⟩, ⟨decodeRow 12 ("72461503", 8), 329⟩, ⟨decodeRow 12 ("24615073", 8), 330⟩])))))
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("46150723", 6), 331⟩, ⟨decodeRow 12 ("34615027", 6), 330⟩, ⟨decodeRow 12 ("73461520", 8), 329⟩, ⟨decodeRow 12 ("34615270", 8), 330⟩, ⟨decodeRow 12 ("46152730", 8), 331⟩, ⟨decodeRow 12 ("61527340", 8), 332⟩, ⟨decodeRow 12 ("15273460", 6), 333⟩, ⟨decodeRow 12 ("01527364", 8), 332⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("15273604", 8), 333⟩, ⟨decodeRow 12 ("52736014", 8), 334⟩, ⟨decodeRow 12 ("27360154", 8), 335⟩, ⟨decodeRow 12 ("73601524", 6), 336⟩])
                  (.leaf [⟨decodeRow 12 ("47360125", 8), 335⟩, ⟨decodeRow 12 ("73601245", 8), 336⟩, ⟨decodeRow 12 ("36012475", 8), 337⟩, ⟨decodeRow 12 ("60124735", 8), 338⟩, ⟨decodeRow 12 ("01247365", 6), 339⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("50124763", 8), 338⟩, ⟨decodeRow 12 ("01247653", 8), 339⟩, ⟨decodeRow 12 ("12476503", 8), 340⟩, ⟨decodeRow 12 ("24765013", 6), 341⟩])
                  (.leaf [⟨decodeRow 12 ("32476510", 8), 340⟩, ⟨decodeRow 12 ("24765130", 8), 341⟩, ⟨decodeRow 12 ("47651320", 8), 342⟩, ⟨decodeRow 12 ("76513240", 6), 343⟩, ⟨decodeRow 12 ("07651342", 8), 342⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76513402", 8), 343⟩, ⟨decodeRow 12 ("65134072", 8), 344⟩, ⟨decodeRow 12 ("51340762", 8), 345⟩, ⟨decodeRow 12 ("13407652", 6), 346⟩])
                  (.leaf [⟨decodeRow 12 ("21340756", 8), 345⟩, ⟨decodeRow 12 ("13407526", 8), 346⟩, ⟨decodeRow 12 ("34075216", 8), 347⟩, ⟨decodeRow 12 ("40752136", 6), 348⟩, ⟨decodeRow 12 ("64075231", 8), 347⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40752361", 8), 348⟩, ⟨decodeRow 12 ("07523641", 6), 349⟩, ⟨decodeRow 12 ("10752346", 8), 348⟩, ⟨decodeRow 12 ("07523416", 8), 349⟩])
                  (.leaf [⟨decodeRow 12 ("75234106", 8), 350⟩, ⟨decodeRow 12 ("52341076", 8), 351⟩, ⟨decodeRow 12 ("23410756", 6), 352⟩, ⟨decodeRow 12 ("62341057", 6), 351⟩, ⟨decodeRow 12 ("76234150", 8), 350⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("62341570", 8), 351⟩, ⟨decodeRow 12 ("23415760", 8), 352⟩, ⟨decodeRow 12 ("34157620", 8), 353⟩, ⟨decodeRow 12 ("41576230", 6), 354⟩])
                  (.leaf [⟨decodeRow 12 ("04157632", 8), 353⟩, ⟨decodeRow 12 ("41576302", 8), 354⟩, ⟨decodeRow 12 ("15763042", 8), 355⟩, ⟨decodeRow 12 ("57630412", 8), 356⟩, ⟨decodeRow 12 ("76304152", 6), 357⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27630451", 8), 356⟩, ⟨decodeRow 12 ("76304521", 8), 357⟩, ⟨decodeRow 12 ("63045271", 8), 358⟩, ⟨decodeRow 12 ("30452761", 6), 359⟩])
                  (.leaf [⟨decodeRow 12 ("13045267", 6), 358⟩, ⟨decodeRow 12 ("71304562", 8), 357⟩, ⟨decodeRow 12 ("13045672", 8), 358⟩, ⟨decodeRow 12 ("30456712", 8), 359⟩, ⟨decodeRow 12 ("04567132", 8), 360⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45671302", 6), 361⟩, ⟨decodeRow 12 ("24567103", 8), 360⟩, ⟨decodeRow 12 ("45671023", 8), 361⟩, ⟨decodeRow 12 ("56710243", 8), 362⟩])
                  (.leaf [⟨decodeRow 12 ("67102453", 6), 363⟩, ⟨decodeRow 12 ("36710254", 8), 362⟩, ⟨decodeRow 12 ("67102534", 8), 363⟩, ⟨decodeRow 12 ("71025364", 8), 364⟩, ⟨decodeRow 12 ("10253674", 8), 365⟩]))))))
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("02536714", 8), 366⟩, ⟨decodeRow 12 ("25367104", 6), 367⟩, ⟨decodeRow 12 ("42536701", 8), 366⟩, ⟨decodeRow 12 ("25367041", 8), 367⟩, ⟨decodeRow 12 ("53670421", 8), 368⟩, ⟨decodeRow 12 ("36704251", 6), 369⟩, ⟨decodeRow 12 ("13670452", 8), 368⟩, ⟨decodeRow 12 ("36704512", 8), 369⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67045132", 8), 370⟩, ⟨decodeRow 12 ("70451362", 6), 371⟩, ⟨decodeRow 12 ("27045163", 8), 370⟩, ⟨decodeRow 12 ("70451623", 8), 371⟩])
                  (.leaf [⟨decodeRow 12 ("04516273", 8), 372⟩, ⟨decodeRow 12 ("45162703", 8), 373⟩, ⟨decodeRow 12 ("51627043", 6), 374⟩, ⟨decodeRow 12 ("35162740", 8), 373⟩, ⟨decodeRow 12 ("51627430", 8), 374⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("16274350", 8), 375⟩, ⟨decodeRow 12 ("62743510", 6), 376⟩, ⟨decodeRow 12 ("06274315", 8), 375⟩, ⟨decodeRow 12 ("62743105", 8), 376⟩])
                  (.leaf [⟨decodeRow 12 ("27431065", 8), 377⟩, ⟨decodeRow 12 ("74310625", 6), 378⟩, ⟨decodeRow 12 ("57431026", 8), 377⟩, ⟨decodeRow 12 ("74310256", 8), 378⟩, ⟨decodeRow 12 ("43102576", 8), 379⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("31025746", 6), 380⟩, ⟨decodeRow 12 ("63102547", 6), 379⟩, ⟨decodeRow 12 ("76310245", 8), 378⟩, ⟨decodeRow 12 ("63102475", 8), 379⟩])
                  (.leaf [⟨decodeRow 12 ("31024765", 8), 380⟩, ⟨decodeRow 12 ("10247635", 8), 381⟩, ⟨decodeRow 12 ("02476315", 8), 382⟩, ⟨decodeRow 12 ("24763105", 6), 383⟩, ⟨decodeRow 12 ("52476301", 8), 382⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("24763051", 8), 383⟩, ⟨decodeRow 12 ("47630521", 8), 384⟩, ⟨decodeRow 12 ("76305241", 6), 385⟩, ⟨decodeRow 12 ("17630542", 8), 384⟩])
                  (.leaf [⟨decodeRow 12 ("76305412", 8), 385⟩, ⟨decodeRow 12 ("63054172", 8), 386⟩, ⟨decodeRow 12 ("30541762", 8), 387⟩, ⟨decodeRow 12 ("05417632", 6), 388⟩, ⟨decodeRow 12 ("20541736", 8), 387⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("05417326", 8), 388⟩, ⟨decodeRow 12 ("54173206", 8), 389⟩, ⟨decodeRow 12 ("41732056", 6), 390⟩, ⟨decodeRow 12 ("64173250", 8), 389⟩])
                  (.leaf [⟨decodeRow 12 ("41732560", 8), 390⟩, ⟨decodeRow 12 ("17325640", 8), 391⟩, ⟨decodeRow 12 ("73256410", 6), 392⟩, ⟨decodeRow 12 ("07325614", 8), 391⟩, ⟨decodeRow 12 ("73256104", 8), 392⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("32561074", 8), 393⟩, ⟨decodeRow 12 ("25610734", 6), 394⟩, ⟨decodeRow 12 ("42561037", 6), 393⟩, ⟨decodeRow 12 ("74256130", 8), 392⟩])
                  (.leaf [⟨decodeRow 12 ("42561370", 8), 393⟩, ⟨decodeRow 12 ("25613740", 8), 394⟩, ⟨decodeRow 12 ("56137420", 8), 395⟩, ⟨decodeRow 12 ("61374250", 6), 396⟩, ⟨decodeRow 12 ("06137452", 8), 395⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("61374502", 8), 396⟩, ⟨decodeRow 12 ("13745062", 8), 397⟩, ⟨decodeRow 12 ("37450612", 8), 398⟩, ⟨decodeRow 12 ("74506132", 6), 399⟩])
                  (.leaf [⟨decodeRow 12 ("27450631", 8), 398⟩, ⟨decodeRow 12 ("74506321", 8), 399⟩, ⟨decodeRow 12 ("45063271", 8), 400⟩, ⟨decodeRow 12 ("50632741", 8), 401⟩, ⟨decodeRow 12 ("06327451", 6), 402⟩])))))
          (.branch 36
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("10632754", 8), 401⟩, ⟨decodeRow 12 ("06327514", 8), 402⟩, ⟨decodeRow 12 ("63275104", 8), 403⟩, ⟨decodeRow 12 ("32751064", 6), 404⟩])
                  (.leaf [⟨decodeRow 12 ("43275160", 8), 403⟩, ⟨decodeRow 12 ("32751640", 8), 404⟩, ⟨decodeRow 12 ("27516430", 8), 405⟩, ⟨decodeRow 12 ("75164320", 6), 406⟩, ⟨decodeRow 12 ("07516423", 8), 405⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("75164203", 8), 406⟩, ⟨decodeRow 12 ("51642073", 8), 407⟩, ⟨decodeRow 12 ("16420753", 8), 408⟩, ⟨decodeRow 12 ("64207513", 6), 409⟩])
                  (.leaf [⟨decodeRow 12 ("36420715", 8), 408⟩, ⟨decodeRow 12 ("64207135", 8), 409⟩, ⟨decodeRow 12 ("42071365", 8), 410⟩, ⟨decodeRow 12 ("20713645", 6), 411⟩, ⟨decodeRow 12 ("52071346", 8), 410⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("20713456", 8), 411⟩, ⟨decodeRow 12 ("07134526", 6), 412⟩, ⟨decodeRow 12 ("60713425", 8), 411⟩, ⟨decodeRow 12 ("07134265", 8), 412⟩])
                  (.leaf [⟨decodeRow 12 ("71342605", 8), 413⟩, ⟨decodeRow 12 ("13426075", 8), 414⟩, ⟨decodeRow 12 ("34260715", 6), 415⟩, ⟨decodeRow 12 ("53426017", 6), 414⟩, ⟨decodeRow 12 ("75342610", 8), 413⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("53426170", 8), 414⟩, ⟨decodeRow 12 ("34261750", 8), 415⟩, ⟨decodeRow 12 ("42617530", 8), 416⟩, ⟨decodeRow 12 ("26175340", 8), 417⟩])
                  (.leaf [⟨decodeRow 12 ("61753420", 6), 418⟩, ⟨decodeRow 12 ("06175324", 8), 417⟩, ⟨decodeRow 12 ("61753204", 8), 418⟩, ⟨decodeRow 12 ("17532064", 8), 419⟩, ⟨decodeRow 12 ("75320614", 6), 420⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47532016", 8), 419⟩, ⟨decodeRow 12 ("75320146", 8), 420⟩, ⟨decodeRow 12 ("53201476", 8), 421⟩, ⟨decodeRow 12 ("32014756", 8), 422⟩])
                  (.leaf [⟨decodeRow 12 ("20147536", 6), 423⟩, ⟨decodeRow 12 ("62014735", 8), 422⟩, ⟨decodeRow 12 ("20147365", 8), 423⟩, ⟨decodeRow 12 ("01473625", 8), 424⟩, ⟨decodeRow 12 ("14736205", 6), 425⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("51473602", 8), 424⟩, ⟨decodeRow 12 ("14736052", 8), 425⟩, ⟨decodeRow 12 ("47360512", 8), 426⟩, ⟨decodeRow 12 ("73605142", 6), 427⟩])
                  (.leaf [⟨decodeRow 12 ("27360541", 8), 426⟩, ⟨decodeRow 12 ("73605421", 8), 427⟩, ⟨decodeRow 12 ("36054271", 8), 428⟩, ⟨decodeRow 12 ("60542731", 8), 429⟩, ⟨decodeRow 12 ("05427361", 6), 430⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("10542763", 8), 429⟩, ⟨decodeRow 12 ("05427613", 8), 430⟩, ⟨decodeRow 12 ("54276103", 6), 431⟩, ⟨decodeRow 12 ("35427601", 8), 430⟩])
                  (.leaf [⟨decodeRow 12 ("54276031", 8), 431⟩, ⟨decodeRow 12 ("42760351", 8), 432⟩, ⟨decodeRow 12 ("27603541", 6), 433⟩, ⟨decodeRow 12 ("12760345", 8), 432⟩, ⟨decodeRow 12 ("27603415", 8), 433⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76034125", 8), 434⟩, ⟨decodeRow 12 ("60341275", 8), 435⟩, ⟨decodeRow 12 ("03412765", 8), 436⟩, ⟨decodeRow 12 ("34127605", 6), 437⟩])
                  (.leaf [⟨decodeRow 12 ("53412706", 8), 436⟩, ⟨decodeRow 12 ("34127056", 8), 437⟩, ⟨decodeRow 12 ("41270536", 8), 438⟩, ⟨decodeRow 12 ("12705346", 6), 439⟩, ⟨decodeRow 12 ("61270543", 8), 438⟩])))))))
      (.branch 142
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("12705463", 8), 439⟩, ⟨decodeRow 12 ("27054613", 8), 440⟩, ⟨decodeRow 12 ("70546123", 6), 441⟩, ⟨decodeRow 12 ("37054621", 8), 440⟩, ⟨decodeRow 12 ("70546231", 8), 441⟩, ⟨decodeRow 12 ("05462371", 8), 442⟩, ⟨decodeRow 12 ("54623701", 8), 443⟩, ⟨decodeRow 12 ("46237051", 6), 444⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14623750", 8), 443⟩, ⟨decodeRow 12 ("46237510", 8), 444⟩, ⟨decodeRow 12 ("62375140", 8), 445⟩, ⟨decodeRow 12 ("23751460", 6), 446⟩])
                  (.leaf [⟨decodeRow 12 ("02375164", 8), 445⟩, ⟨decodeRow 12 ("23751604", 8), 446⟩, ⟨decodeRow 12 ("37516024", 8), 447⟩, ⟨decodeRow 12 ("75160234", 6), 448⟩, ⟨decodeRow 12 ("47516032", 8), 447⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("75160342", 8), 448⟩, ⟨decodeRow 12 ("51603472", 8), 449⟩, ⟨decodeRow 12 ("16034752", 6), 450⟩, ⟨decodeRow 12 ("21603457", 6), 449⟩])
                  (.leaf [⟨decodeRow 12 ("72160354", 8), 448⟩, ⟨decodeRow 12 ("21603574", 8), 449⟩, ⟨decodeRow 12 ("16035724", 8), 450⟩, ⟨decodeRow 12 ("60357214", 8), 451⟩, ⟨decodeRow 12 ("03572164", 6), 452⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40357261", 8), 451⟩, ⟨decodeRow 12 ("03572641", 8), 452⟩, ⟨decodeRow 12 ("35726401", 8), 453⟩, ⟨decodeRow 12 ("57264031", 8), 454⟩])
                  (.leaf [⟨decodeRow 12 ("72640351", 6), 455⟩, ⟨decodeRow 12 ("17264053", 8), 454⟩, ⟨decodeRow 12 ("72640513", 8), 455⟩, ⟨decodeRow 12 ("26405173", 8), 456⟩, ⟨decodeRow 12 ("64051723", 8), 457⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40517263", 6), 458⟩, ⟨decodeRow 12 ("34051762", 8), 457⟩, ⟨decodeRow 12 ("40517632", 8), 458⟩, ⟨decodeRow 12 ("05176342", 8), 459⟩])
                  (.leaf [⟨decodeRow 12 ("51763402", 6), 460⟩, ⟨decodeRow 12 ("25176304", 8), 459⟩, ⟨decodeRow 12 ("51763024", 8), 460⟩, ⟨decodeRow 12 ("17630254", 8), 461⟩, ⟨decodeRow 12 ("76302514", 6), 462⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47630215", 8), 461⟩, ⟨decodeRow 12 ("76302145", 8), 462⟩, ⟨decodeRow 12 ("63021475", 8), 463⟩, ⟨decodeRow 12 ("30214765", 8), 464⟩])
                  (.leaf [⟨decodeRow 12 ("02147635", 6), 465⟩, ⟨decodeRow 12 ("50214736", 8), 464⟩, ⟨decodeRow 12 ("02147356", 8), 465⟩, ⟨decodeRow 12 ("21473506", 8), 466⟩, ⟨decodeRow 12 ("14735026", 6), 467⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("61473520", 8), 466⟩, ⟨decodeRow 12 ("14735260", 8), 467⟩, ⟨decodeRow 12 ("47352610", 6), 468⟩, ⟨decodeRow 12 ("04735216", 8), 467⟩])
                  (.leaf [⟨decodeRow 12 ("47352106", 8), 468⟩, ⟨decodeRow 12 ("73521046", 8), 469⟩, ⟨decodeRow 12 ("35210476", 8), 470⟩, ⟨decodeRow 12 ("52104736", 6), 471⟩, ⟨decodeRow 12 ("65210437", 6), 470⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76521034", 8), 469⟩, ⟨decodeRow 12 ("65210374", 8), 470⟩, ⟨decodeRow 12 ("52103764", 8), 471⟩, ⟨decodeRow 12 ("21037654", 8), 472⟩])
                  (.leaf [⟨decodeRow 12 ("10376524", 6), 473⟩, ⟨decodeRow 12 ("41037625", 8), 472⟩, ⟨decodeRow 12 ("10376245", 8), 473⟩, ⟨decodeRow 12 ("03762415", 8), 474⟩, ⟨decodeRow 12 ("37624105", 8), 475⟩])))))
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("76241035", 6), 476⟩, ⟨decodeRow 12 ("57624130", 8), 475⟩, ⟨decodeRow 12 ("76241350", 8), 476⟩, ⟨decodeRow 12 ("62413570", 8), 477⟩, ⟨decodeRow 12 ("24135760", 6), 478⟩, ⟨decodeRow 12 ("02413567", 6), 477⟩, ⟨decodeRow 12 ("70241365", 8), 476⟩, ⟨decodeRow 12 ("02413675", 8), 477⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("24136705", 8), 478⟩, ⟨decodeRow 12 ("41367025", 8), 479⟩, ⟨decodeRow 12 ("13670245", 8), 480⟩, ⟨decodeRow 12 ("36702415", 6), 481⟩])
                  (.leaf [⟨decodeRow 12 ("53670214", 8), 480⟩, ⟨decodeRow 12 ("36702154", 8), 481⟩, ⟨decodeRow 12 ("67021534", 6), 482⟩, ⟨decodeRow 12 ("46702135", 8), 481⟩, ⟨decodeRow 12 ("67021345", 8), 482⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("70213465", 8), 483⟩, ⟨decodeRow 12 ("02134675", 8), 484⟩, ⟨decodeRow 12 ("21346705", 8), 485⟩, ⟨decodeRow 12 ("13467025", 6), 486⟩])
                  (.leaf [⟨decodeRow 12 ("51346720", 8), 485⟩, ⟨decodeRow 12 ("13467250", 8), 486⟩, ⟨decodeRow 12 ("34672510", 8), 487⟩, ⟨decodeRow 12 ("46725130", 6), 488⟩, ⟨decodeRow 12 ("04672531", 8), 487⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("46725301", 8), 488⟩, ⟨decodeRow 12 ("67253041", 8), 489⟩, ⟨decodeRow 12 ("72530461", 6), 490⟩, ⟨decodeRow 12 ("17253064", 8), 489⟩])
                  (.leaf [⟨decodeRow 12 ("72530614", 8), 490⟩, ⟨decodeRow 12 ("25306174", 8), 491⟩, ⟨decodeRow 12 ("53061724", 6), 492⟩, ⟨decodeRow 12 ("45306127", 6), 491⟩, ⟨decodeRow 12 ("74530621", 8), 490⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45306271", 8), 491⟩, ⟨decodeRow 12 ("53062741", 8), 492⟩, ⟨decodeRow 12 ("30627451", 8), 493⟩, ⟨decodeRow 12 ("06274531", 8), 494⟩])
                  (.leaf [⟨decodeRow 12 ("62745301", 6), 495⟩, ⟨decodeRow 12 ("16274503", 8), 494⟩, ⟨decodeRow 12 ("62745013", 8), 495⟩, ⟨decodeRow 12 ("27450163", 8), 496⟩, ⟨decodeRow 12 ("74501623", 6), 497⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("37450126", 8), 496⟩, ⟨decodeRow 12 ("74501236", 8), 497⟩, ⟨decodeRow 12 ("45012376", 8), 498⟩, ⟨decodeRow 12 ("50123746", 8), 499⟩])
                  (.leaf [⟨decodeRow 12 ("01237456", 6), 500⟩, ⟨decodeRow 12 ("60123754", 8), 499⟩, ⟨decodeRow 12 ("01237564", 8), 500⟩, ⟨decodeRow 12 ("12375604", 6), 501⟩, ⟨decodeRow 12 ("41237506", 8), 500⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("12375046", 8), 501⟩, ⟨decodeRow 12 ("23750416", 8), 502⟩, ⟨decodeRow 12 ("37504126", 6), 503⟩, ⟨decodeRow 12 ("63750421", 8), 502⟩])
                  (.leaf [⟨decodeRow 12 ("37504261", 8), 503⟩, ⟨decodeRow 12 ("75042631", 8), 504⟩, ⟨decodeRow 12 ("50426371", 8), 505⟩, ⟨decodeRow 12 ("04263751", 8), 506⟩, ⟨decodeRow 12 ("42637501", 6), 507⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14263705", 8), 506⟩, ⟨decodeRow 12 ("42637015", 8), 507⟩, ⟨decodeRow 12 ("26370145", 8), 508⟩, ⟨decodeRow 12 ("63701425", 6), 509⟩])
                  (.leaf [⟨decodeRow 12 ("56370124", 8), 508⟩, ⟨decodeRow 12 ("63701254", 8), 509⟩, ⟨decodeRow 12 ("37012564", 8), 510⟩, ⟨decodeRow 12 ("70125634", 6), 511⟩, ⟨decodeRow 12 ("47012536", 8), 510⟩]))))))
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("70125346", 8), 511⟩, ⟨decodeRow 12 ("01253476", 8), 512⟩, ⟨decodeRow 12 ("12534706", 8), 513⟩, ⟨decodeRow 12 ("25347016", 6), 514⟩, ⟨decodeRow 12 ("62534710", 8), 513⟩, ⟨decodeRow 12 ("25347160", 8), 514⟩, ⟨decodeRow 12 ("53471620", 8), 515⟩, ⟨decodeRow 12 ("34716250", 6), 516⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03471652", 8), 515⟩, ⟨decodeRow 12 ("34716502", 8), 516⟩, ⟨decodeRow 12 ("47165032", 8), 517⟩, ⟨decodeRow 12 ("71650342", 6), 518⟩])
                  (.leaf [⟨decodeRow 12 ("27165043", 8), 517⟩, ⟨decodeRow 12 ("71650423", 8), 518⟩, ⟨decodeRow 12 ("16504273", 8), 519⟩, ⟨decodeRow 12 ("65042713", 6), 520⟩, ⟨decodeRow 12 ("36504217", 6), 519⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("73650412", 8), 518⟩, ⟨decodeRow 12 ("36504172", 8), 519⟩, ⟨decodeRow 12 ("65041732", 8), 520⟩, ⟨decodeRow 12 ("50417362", 8), 521⟩])
                  (.leaf [⟨decodeRow 12 ("04173652", 6), 522⟩, ⟨decodeRow 12 ("20417356", 8), 521⟩, ⟨decodeRow 12 ("04173526", 8), 522⟩, ⟨decodeRow 12 ("41735206", 8), 523⟩, ⟨decodeRow 12 ("17352046", 8), 524⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("73520416", 6), 525⟩, ⟨decodeRow 12 ("67352014", 8), 524⟩, ⟨decodeRow 12 ("73520164", 8), 525⟩, ⟨decodeRow 12 ("35201674", 8), 526⟩])
                  (.leaf [⟨decodeRow 12 ("52016734", 8), 527⟩, ⟨decodeRow 12 ("20167354", 6), 528⟩, ⟨decodeRow 12 ("42016753", 8), 527⟩, ⟨decodeRow 12 ("20167543", 8), 528⟩, ⟨decodeRow 12 ("01675423", 8), 529⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("16754203", 6), 530⟩, ⟨decodeRow 12 ("31675402", 8), 529⟩, ⟨decodeRow 12 ("16754032", 8), 530⟩, ⟨decodeRow 12 ("67540312", 8), 531⟩])
                  (.leaf [⟨decodeRow 12 ("75403162", 6), 532⟩, ⟨decodeRow 12 ("27540361", 8), 531⟩, ⟨decodeRow 12 ("75403621", 8), 532⟩, ⟨decodeRow 12 ("54036271", 8), 533⟩, ⟨decodeRow 12 ("40362751", 6), 534⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14036257", 6), 533⟩, ⟨decodeRow 12 ("71403652", 8), 532⟩, ⟨decodeRow 12 ("14036572", 8), 533⟩, ⟨decodeRow 12 ("40365712", 8), 534⟩])
                  (.leaf [⟨decodeRow 12 ("03657142", 8), 535⟩, ⟨decodeRow 12 ("36571402", 6), 536⟩, ⟨decodeRow 12 ("23657104", 8), 535⟩, ⟨decodeRow 12 ("36571024", 8), 536⟩, ⟨decodeRow 12 ("65710234", 8), 537⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("57102364", 6), 538⟩, ⟨decodeRow 12 ("45710263", 8), 537⟩, ⟨decodeRow 12 ("57102643", 8), 538⟩, ⟨decodeRow 12 ("71026453", 8), 539⟩])
                  (.leaf [⟨decodeRow 12 ("10264573", 8), 540⟩, ⟨decodeRow 12 ("02645713", 6), 541⟩, ⟨decodeRow 12 ("30264517", 6), 540⟩, ⟨decodeRow 12 ("73026415", 8), 539⟩, ⟨decodeRow 12 ("30264175", 8), 540⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("02641735", 8), 541⟩, ⟨decodeRow 12 ("26417305", 8), 542⟩, ⟨decodeRow 12 ("64173025", 8), 543⟩, ⟨decodeRow 12 ("41730265", 6), 544⟩])
                  (.leaf [⟨decodeRow 12 ("54173062", 8), 543⟩, ⟨decodeRow 12 ("41730652", 8), 544⟩, ⟨decodeRow 12 ("17306542", 8), 545⟩, ⟨decodeRow 12 ("73065412", 6), 546⟩, ⟨decodeRow 12 ("27306514", 8), 545⟩])))))
          (.branch 36
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("73065124", 8), 546⟩, ⟨decodeRow 12 ("30651274", 8), 547⟩, ⟨decodeRow 12 ("06512734", 8), 548⟩, ⟨decodeRow 12 ("65127304", 6), 549⟩])
                  (.leaf [⟨decodeRow 12 ("46512703", 8), 548⟩, ⟨decodeRow 12 ("65127043", 8), 549⟩, ⟨decodeRow 12 ("51270463", 8), 550⟩, ⟨decodeRow 12 ("12704653", 6), 551⟩, ⟨decodeRow 12 ("31270456", 8), 550⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("12704536", 8), 551⟩, ⟨decodeRow 12 ("27045316", 8), 552⟩, ⟨decodeRow 12 ("70453126", 6), 553⟩, ⟨decodeRow 12 ("67045321", 8), 552⟩])
                  (.leaf [⟨decodeRow 12 ("70453261", 8), 553⟩, ⟨decodeRow 12 ("04532671", 8), 554⟩, ⟨decodeRow 12 ("45326701", 8), 555⟩, ⟨decodeRow 12 ("53267041", 6), 556⟩, ⟨decodeRow 12 ("15326740", 8), 555⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("53267410", 8), 556⟩, ⟨decodeRow 12 ("32674150", 6), 557⟩, ⟨decodeRow 12 ("03267451", 8), 556⟩, ⟨decodeRow 12 ("32674501", 8), 557⟩])
                  (.leaf [⟨decodeRow 12 ("26745031", 8), 558⟩, ⟨decodeRow 12 ("67450321", 6), 559⟩, ⟨decodeRow 12 ("16745023", 8), 558⟩, ⟨decodeRow 12 ("67450213", 8), 559⟩, ⟨decodeRow 12 ("74502163", 8), 560⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45021673", 8), 561⟩, ⟨decodeRow 12 ("50216743", 8), 562⟩, ⟨decodeRow 12 ("02167453", 6), 563⟩, ⟨decodeRow 12 ("30216754", 8), 562⟩])
                  (.leaf [⟨decodeRow 12 ("02167534", 8), 563⟩, ⟨decodeRow 12 ("21675304", 8), 564⟩, ⟨decodeRow 12 ("16753024", 6), 565⟩, ⟨decodeRow 12 ("41675320", 8), 564⟩, ⟨decodeRow 12 ("16753240", 8), 565⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67532410", 8), 566⟩, ⟨decodeRow 12 ("75324160", 6), 567⟩, ⟨decodeRow 12 ("07532461", 8), 566⟩, ⟨decodeRow 12 ("75324601", 8), 567⟩])
                  (.leaf [⟨decodeRow 12 ("53246071", 8), 568⟩, ⟨decodeRow 12 ("32460751", 8), 569⟩, ⟨decodeRow 12 ("24607531", 6), 570⟩, ⟨decodeRow 12 ("12460735", 8), 569⟩, ⟨decodeRow 12 ("24607315", 8), 570⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("46073125", 8), 571⟩, ⟨decodeRow 12 ("60731245", 6), 572⟩, ⟨decodeRow 12 ("56073142", 8), 571⟩, ⟨decodeRow 12 ("60731452", 8), 572⟩])
                  (.leaf [⟨decodeRow 12 ("07314562", 8), 573⟩, ⟨decodeRow 12 ("73145602", 6), 574⟩, ⟨decodeRow 12 ("27314506", 8), 573⟩, ⟨decodeRow 12 ("73145026", 8), 574⟩, ⟨decodeRow 12 ("31450276", 8), 575⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14502736", 6), 576⟩, ⟨decodeRow 12 ("61450237", 6), 575⟩, ⟨decodeRow 12 ("76145032", 8), 574⟩, ⟨decodeRow 12 ("61450372", 8), 575⟩])
                  (.leaf [⟨decodeRow 12 ("14503762", 8), 576⟩, ⟨decodeRow 12 ("45037612", 8), 577⟩, ⟨decodeRow 12 ("50376142", 6), 578⟩, ⟨decodeRow 12 ("25037641", 8), 577⟩, ⟨decodeRow 12 ("50376421", 8), 578⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03764251", 8), 579⟩, ⟨decodeRow 12 ("37642501", 8), 580⟩, ⟨decodeRow 12 ("76425031", 6), 581⟩, ⟨decodeRow 12 ("17642530", 8), 580⟩])
                  (.leaf [⟨decodeRow 12 ("76425310", 8), 581⟩, ⟨decodeRow 12 ("64253170", 8), 582⟩, ⟨decodeRow 12 ("42531760", 8), 583⟩, ⟨decodeRow 12 ("25317640", 6), 584⟩, ⟨decodeRow 12 ("02531746", 8), 583⟩])))))))))
  (.branch 570
    (.branch 285
      (.branch 142
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("25317406", 8), 584⟩, ⟨decodeRow 12 ("53174026", 8), 585⟩, ⟨decodeRow 12 ("31740256", 6), 586⟩, ⟨decodeRow 12 ("63174052", 8), 585⟩, ⟨decodeRow 12 ("31740562", 8), 586⟩, ⟨decodeRow 12 ("17405632", 8), 587⟩, ⟨decodeRow 12 ("74056312", 6), 588⟩, ⟨decodeRow 12 ("27405613", 8), 587⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74056123", 8), 588⟩, ⟨decodeRow 12 ("40561273", 8), 589⟩, ⟨decodeRow 12 ("05612743", 8), 590⟩, ⟨decodeRow 12 ("56127403", 6), 591⟩])
                  (.leaf [⟨decodeRow 12 ("35612704", 8), 590⟩, ⟨decodeRow 12 ("56127034", 8), 591⟩, ⟨decodeRow 12 ("61270354", 8), 592⟩, ⟨decodeRow 12 ("12703564", 6), 593⟩, ⟨decodeRow 12 ("41270365", 8), 592⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("12703645", 8), 593⟩, ⟨decodeRow 12 ("27036415", 6), 594⟩, ⟨decodeRow 12 ("52703614", 8), 593⟩, ⟨decodeRow 12 ("27036154", 8), 594⟩])
                  (.leaf [⟨decodeRow 12 ("70361524", 8), 595⟩, ⟨decodeRow 12 ("03615274", 8), 596⟩, ⟨decodeRow 12 ("36152704", 6), 597⟩, ⟨decodeRow 12 ("43615207", 6), 596⟩, ⟨decodeRow 12 ("74361502", 8), 595⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("43615072", 8), 596⟩, ⟨decodeRow 12 ("36150742", 8), 597⟩, ⟨decodeRow 12 ("61507432", 8), 598⟩, ⟨decodeRow 12 ("15074362", 8), 599⟩])
                  (.leaf [⟨decodeRow 12 ("50743612", 6), 600⟩, ⟨decodeRow 12 ("25074316", 8), 599⟩, ⟨decodeRow 12 ("50743126", 8), 600⟩, ⟨decodeRow 12 ("07431256", 8), 601⟩, ⟨decodeRow 12 ("74312506", 6), 602⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67431205", 8), 601⟩, ⟨decodeRow 12 ("74312065", 8), 602⟩, ⟨decodeRow 12 ("43120675", 8), 603⟩, ⟨decodeRow 12 ("31206745", 8), 604⟩])
                  (.leaf [⟨decodeRow 12 ("12067435", 6), 605⟩, ⟨decodeRow 12 ("51206734", 8), 604⟩, ⟨decodeRow 12 ("12067354", 8), 605⟩, ⟨decodeRow 12 ("20673514", 8), 606⟩, ⟨decodeRow 12 ("06735124", 6), 607⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40673521", 8), 606⟩, ⟨decodeRow 12 ("06735241", 8), 607⟩, ⟨decodeRow 12 ("67352401", 8), 608⟩, ⟨decodeRow 12 ("73524061", 6), 609⟩])
                  (.leaf [⟨decodeRow 12 ("17352460", 8), 608⟩, ⟨decodeRow 12 ("73524610", 8), 609⟩, ⟨decodeRow 12 ("35246170", 8), 610⟩, ⟨decodeRow 12 ("52461730", 8), 611⟩, ⟨decodeRow 12 ("24617350", 6), 612⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("02461753", 8), 611⟩, ⟨decodeRow 12 ("24617503", 8), 612⟩, ⟨decodeRow 12 ("46175023", 6), 613⟩, ⟨decodeRow 12 ("34617520", 8), 612⟩])
                  (.leaf [⟨decodeRow 12 ("46175230", 8), 613⟩, ⟨decodeRow 12 ("61752340", 8), 614⟩, ⟨decodeRow 12 ("17523460", 6), 615⟩, ⟨decodeRow 12 ("01752364", 8), 614⟩, ⟨decodeRow 12 ("17523604", 8), 615⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("75236014", 8), 616⟩, ⟨decodeRow 12 ("52360174", 8), 617⟩, ⟨decodeRow 12 ("23601754", 8), 618⟩, ⟨decodeRow 12 ("36017524", 6), 619⟩])
                  (.leaf [⟨decodeRow 12 ("43601725", 8), 618⟩, ⟨decodeRow 12 ("36017245", 8), 619⟩, ⟨decodeRow 12 ("60172435", 8), 620⟩, ⟨decodeRow 12 ("01724365", 6), 621⟩, ⟨decodeRow 12 ("50172463", 8), 620⟩])))))
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("01724653", 8), 621⟩, ⟨decodeRow 12 ("17246503", 8), 622⟩, ⟨decodeRow 12 ("72465013", 6), 623⟩, ⟨decodeRow 12 ("37246510", 8), 622⟩, ⟨decodeRow 12 ("72465130", 8), 623⟩, ⟨decodeRow 12 ("24651370", 8), 624⟩, ⟨decodeRow 12 ("46513720", 8), 625⟩, ⟨decodeRow 12 ("65137240", 6), 626⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("06513742", 8), 625⟩, ⟨decodeRow 12 ("65137402", 8), 626⟩, ⟨decodeRow 12 ("51374062", 8), 627⟩, ⟨decodeRow 12 ("13740652", 6), 628⟩])
                  (.leaf [⟨decodeRow 12 ("21374056", 8), 627⟩, ⟨decodeRow 12 ("13740526", 8), 628⟩, ⟨decodeRow 12 ("37405216", 8), 629⟩, ⟨decodeRow 12 ("74052136", 6), 630⟩, ⟨decodeRow 12 ("67405231", 8), 629⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74052361", 8), 630⟩, ⟨decodeRow 12 ("40523671", 8), 631⟩, ⟨decodeRow 12 ("05236741", 6), 632⟩, ⟨decodeRow 12 ("10523647", 6), 631⟩])
                  (.leaf [⟨decodeRow 12 ("71052346", 8), 630⟩, ⟨decodeRow 12 ("10523476", 8), 631⟩, ⟨decodeRow 12 ("05234716", 8), 632⟩, ⟨decodeRow 12 ("52347106", 8), 633⟩, ⟨decodeRow 12 ("23471056", 6), 634⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("62347150", 8), 633⟩, ⟨decodeRow 12 ("23471560", 8), 634⟩, ⟨decodeRow 12 ("34715620", 8), 635⟩, ⟨decodeRow 12 ("47156230", 6), 636⟩])
                  (.leaf [⟨decodeRow 12 ("04715632", 8), 635⟩, ⟨decodeRow 12 ("47156302", 8), 636⟩, ⟨decodeRow 12 ("71563042", 8), 637⟩, ⟨decodeRow 12 ("15630472", 8), 638⟩, ⟨decodeRow 12 ("56304712", 8), 639⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("63047152", 6), 640⟩, ⟨decodeRow 12 ("26304751", 8), 639⟩, ⟨decodeRow 12 ("63047521", 8), 640⟩, ⟨decodeRow 12 ("30475261", 6), 641⟩])
                  (.leaf [⟨decodeRow 12 ("13047562", 8), 640⟩, ⟨decodeRow 12 ("30475612", 8), 641⟩, ⟨decodeRow 12 ("04756132", 8), 642⟩, ⟨decodeRow 12 ("47561302", 6), 643⟩, ⟨decodeRow 12 ("24756103", 8), 642⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47561023", 8), 643⟩, ⟨decodeRow 12 ("75610243", 8), 644⟩, ⟨decodeRow 12 ("56102473", 8), 645⟩, ⟨decodeRow 12 ("61024753", 6), 646⟩])
                  (.leaf [⟨decodeRow 12 ("36102457", 6), 645⟩, ⟨decodeRow 12 ("73610254", 8), 644⟩, ⟨decodeRow 12 ("36102574", 8), 645⟩, ⟨decodeRow 12 ("61025734", 8), 646⟩, ⟨decodeRow 12 ("10257364", 8), 647⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("02573614", 8), 648⟩, ⟨decodeRow 12 ("25736104", 6), 649⟩, ⟨decodeRow 12 ("42573601", 8), 648⟩, ⟨decodeRow 12 ("25736041", 8), 649⟩])
                  (.leaf [⟨decodeRow 12 ("57360421", 8), 650⟩, ⟨decodeRow 12 ("73604251", 6), 651⟩, ⟨decodeRow 12 ("17360452", 8), 650⟩, ⟨decodeRow 12 ("73604512", 8), 651⟩, ⟨decodeRow 12 ("36045172", 8), 652⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("60451732", 8), 653⟩, ⟨decodeRow 12 ("04517362", 6), 654⟩, ⟨decodeRow 12 ("20451763", 8), 653⟩, ⟨decodeRow 12 ("04517623", 8), 654⟩])
                  (.leaf [⟨decodeRow 12 ("45176203", 8), 655⟩, ⟨decodeRow 12 ("51762043", 6), 656⟩, ⟨decodeRow 12 ("35176240", 8), 655⟩, ⟨decodeRow 12 ("51762430", 8), 656⟩, ⟨decodeRow 12 ("17624350", 8), 657⟩]))))))
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("76243510", 6), 658⟩, ⟨decodeRow 12 ("07624315", 8), 657⟩, ⟨decodeRow 12 ("76243105", 8), 658⟩, ⟨decodeRow 12 ("62431075", 8), 659⟩, ⟨decodeRow 12 ("24310765", 8), 660⟩, ⟨decodeRow 12 ("43107625", 6), 661⟩, ⟨decodeRow 12 ("54310726", 8), 660⟩, ⟨decodeRow 12 ("43107256", 8), 661⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("31072546", 6), 662⟩, ⟨decodeRow 12 ("63107245", 8), 661⟩, ⟨decodeRow 12 ("31072465", 8), 662⟩, ⟨decodeRow 12 ("10724635", 8), 663⟩])
                  (.leaf [⟨decodeRow 12 ("07246315", 8), 664⟩, ⟨decodeRow 12 ("72463105", 6), 665⟩, ⟨decodeRow 12 ("57246301", 8), 664⟩, ⟨decodeRow 12 ("72463051", 8), 665⟩, ⟨decodeRow 12 ("24630571", 8), 666⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("46305721", 8), 667⟩, ⟨decodeRow 12 ("63057241", 6), 668⟩, ⟨decodeRow 12 ("16305742", 8), 667⟩, ⟨decodeRow 12 ("63057412", 8), 668⟩])
                  (.leaf [⟨decodeRow 12 ("30574162", 8), 669⟩, ⟨decodeRow 12 ("05741632", 6), 670⟩, ⟨decodeRow 12 ("20574136", 8), 669⟩, ⟨decodeRow 12 ("05741326", 8), 670⟩, ⟨decodeRow 12 ("57413206", 8), 671⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74132056", 6), 672⟩, ⟨decodeRow 12 ("67413250", 8), 671⟩, ⟨decodeRow 12 ("74132560", 8), 672⟩, ⟨decodeRow 12 ("41325670", 8), 673⟩])
                  (.leaf [⟨decodeRow 12 ("13256740", 8), 674⟩, ⟨decodeRow 12 ("32567410", 6), 675⟩, ⟨decodeRow 12 ("03256714", 8), 674⟩, ⟨decodeRow 12 ("32567104", 8), 675⟩, ⟨decodeRow 12 ("25671034", 6), 676⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("42567130", 8), 675⟩, ⟨decodeRow 12 ("25671340", 8), 676⟩, ⟨decodeRow 12 ("56713420", 8), 677⟩, ⟨decodeRow 12 ("67134250", 6), 678⟩])
                  (.leaf [⟨decodeRow 12 ("06713452", 8), 677⟩, ⟨decodeRow 12 ("67134502", 8), 678⟩, ⟨decodeRow 12 ("71345062", 8), 679⟩, ⟨decodeRow 12 ("13450672", 8), 680⟩, ⟨decodeRow 12 ("34506712", 8), 681⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45067132", 6), 682⟩, ⟨decodeRow 12 ("24506731", 8), 681⟩, ⟨decodeRow 12 ("45067321", 8), 682⟩, ⟨decodeRow 12 ("50673241", 8), 683⟩])
                  (.leaf [⟨decodeRow 12 ("06732451", 6), 684⟩, ⟨decodeRow 12 ("10673254", 8), 683⟩, ⟨decodeRow 12 ("06732514", 8), 684⟩, ⟨decodeRow 12 ("67325104", 8), 685⟩, ⟨decodeRow 12 ("73251064", 6), 686⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47325160", 8), 685⟩, ⟨decodeRow 12 ("73251640", 8), 686⟩, ⟨decodeRow 12 ("32516470", 8), 687⟩, ⟨decodeRow 12 ("25164730", 8), 688⟩])
                  (.leaf [⟨decodeRow 12 ("51647320", 6), 689⟩, ⟨decodeRow 12 ("05164723", 8), 688⟩, ⟨decodeRow 12 ("51647203", 8), 689⟩, ⟨decodeRow 12 ("16472053", 8), 690⟩, ⟨decodeRow 12 ("64720513", 6), 691⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("36472015", 8), 690⟩, ⟨decodeRow 12 ("64720135", 8), 691⟩, ⟨decodeRow 12 ("47201365", 8), 692⟩, ⟨decodeRow 12 ("72013645", 6), 693⟩])
                  (.leaf [⟨decodeRow 12 ("57201346", 8), 692⟩, ⟨decodeRow 12 ("72013456", 8), 693⟩, ⟨decodeRow 12 ("20134576", 8), 694⟩, ⟨decodeRow 12 ("01345726", 6), 695⟩, ⟨decodeRow 12 ("60134527", 6), 694⟩])))))
          (.branch 36
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76013425", 8), 693⟩, ⟨decodeRow 12 ("60134275", 8), 694⟩, ⟨decodeRow 12 ("01342765", 8), 695⟩, ⟨decodeRow 12 ("13427605", 8), 696⟩])
                  (.leaf [⟨decodeRow 12 ("34276015", 6), 697⟩, ⟨decodeRow 12 ("53427610", 8), 696⟩, ⟨decodeRow 12 ("34276150", 8), 697⟩, ⟨decodeRow 12 ("42761530", 8), 698⟩, ⟨decodeRow 12 ("27615340", 8), 699⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76153420", 6), 700⟩, ⟨decodeRow 12 ("07615324", 8), 699⟩, ⟨decodeRow 12 ("76153204", 8), 700⟩, ⟨decodeRow 12 ("61532074", 8), 701⟩])
                  (.leaf [⟨decodeRow 12 ("15320764", 8), 702⟩, ⟨decodeRow 12 ("53207614", 6), 703⟩, ⟨decodeRow 12 ("45320716", 8), 702⟩, ⟨decodeRow 12 ("53207146", 8), 703⟩, ⟨decodeRow 12 ("32071456", 8), 704⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("20714536", 6), 705⟩, ⟨decodeRow 12 ("62071435", 8), 704⟩, ⟨decodeRow 12 ("20714365", 8), 705⟩, ⟨decodeRow 12 ("07143625", 8), 706⟩])
                  (.leaf [⟨decodeRow 12 ("71436205", 6), 707⟩, ⟨decodeRow 12 ("57143602", 8), 706⟩, ⟨decodeRow 12 ("71436052", 8), 707⟩, ⟨decodeRow 12 ("14360572", 8), 708⟩, ⟨decodeRow 12 ("43605712", 8), 709⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("36057142", 6), 710⟩, ⟨decodeRow 12 ("23605741", 8), 709⟩, ⟨decodeRow 12 ("36057421", 8), 710⟩, ⟨decodeRow 12 ("60574231", 8), 711⟩])
                  (.leaf [⟨decodeRow 12 ("05742361", 6), 712⟩, ⟨decodeRow 12 ("10574263", 8), 711⟩, ⟨decodeRow 12 ("05742613", 8), 712⟩, ⟨decodeRow 12 ("57426103", 6), 713⟩, ⟨decodeRow 12 ("35742601", 8), 712⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("57426031", 8), 713⟩, ⟨decodeRow 12 ("74260351", 8), 714⟩, ⟨decodeRow 12 ("42603571", 8), 715⟩, ⟨decodeRow 12 ("26035741", 6), 716⟩])
                  (.leaf [⟨decodeRow 12 ("12603547", 6), 715⟩, ⟨decodeRow 12 ("71260345", 8), 714⟩, ⟨decodeRow 12 ("12603475", 8), 715⟩, ⟨decodeRow 12 ("26034715", 8), 716⟩, ⟨decodeRow 12 ("60347125", 8), 717⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03471265", 8), 718⟩, ⟨decodeRow 12 ("34712605", 6), 719⟩, ⟨decodeRow 12 ("53471206", 8), 718⟩, ⟨decodeRow 12 ("34712056", 8), 719⟩])
                  (.leaf [⟨decodeRow 12 ("47120536", 8), 720⟩, ⟨decodeRow 12 ("71205346", 6), 721⟩, ⟨decodeRow 12 ("67120543", 8), 720⟩, ⟨decodeRow 12 ("71205463", 8), 721⟩, ⟨decodeRow 12 ("12054673", 8), 722⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("20546713", 8), 723⟩, ⟨decodeRow 12 ("05467123", 6), 724⟩, ⟨decodeRow 12 ("30546721", 8), 723⟩, ⟨decodeRow 12 ("05467231", 8), 724⟩])
                  (.leaf [⟨decodeRow 12 ("54672301", 8), 725⟩, ⟨decodeRow 12 ("46723051", 6), 726⟩, ⟨decodeRow 12 ("14672350", 8), 725⟩, ⟨decodeRow 12 ("46723510", 8), 726⟩, ⟨decodeRow 12 ("67235140", 8), 727⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("72351460", 6), 728⟩, ⟨decodeRow 12 ("07235164", 8), 727⟩, ⟨decodeRow 12 ("72351604", 8), 728⟩, ⟨decodeRow 12 ("23516074", 8), 729⟩])
                  (.leaf [⟨decodeRow 12 ("35160724", 8), 730⟩, ⟨decodeRow 12 ("51607234", 6), 731⟩, ⟨decodeRow 12 ("45160732", 8), 730⟩, ⟨decodeRow 12 ("51607342", 8), 731⟩, ⟨decodeRow 12 ("16073452", 6), 732⟩])))))))
      (.branch 142
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("21607354", 8), 731⟩, ⟨decodeRow 12 ("16073524", 8), 732⟩, ⟨decodeRow 12 ("60735214", 8), 733⟩, ⟨decodeRow 12 ("07352164", 6), 734⟩, ⟨decodeRow 12 ("40735261", 8), 733⟩, ⟨decodeRow 12 ("07352641", 8), 734⟩, ⟨decodeRow 12 ("73526401", 8), 735⟩, ⟨decodeRow 12 ("35264071", 8), 736⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("52640731", 8), 737⟩, ⟨decodeRow 12 ("26407351", 6), 738⟩, ⟨decodeRow 12 ("12640753", 8), 737⟩, ⟨decodeRow 12 ("26407513", 8), 738⟩])
                  (.leaf [⟨decodeRow 12 ("64075123", 8), 739⟩, ⟨decodeRow 12 ("40751263", 6), 740⟩, ⟨decodeRow 12 ("34075162", 8), 739⟩, ⟨decodeRow 12 ("40751632", 8), 740⟩, ⟨decodeRow 12 ("07516342", 8), 741⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("75163402", 6), 742⟩, ⟨decodeRow 12 ("27516304", 8), 741⟩, ⟨decodeRow 12 ("75163024", 8), 742⟩, ⟨decodeRow 12 ("51630274", 8), 743⟩])
                  (.leaf [⟨decodeRow 12 ("16302754", 8), 744⟩, ⟨decodeRow 12 ("63027514", 6), 745⟩, ⟨decodeRow 12 ("46302715", 8), 744⟩, ⟨decodeRow 12 ("63027145", 8), 745⟩, ⟨decodeRow 12 ("30271465", 8), 746⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("02714635", 6), 747⟩, ⟨decodeRow 12 ("50271436", 8), 746⟩, ⟨decodeRow 12 ("02714356", 8), 747⟩, ⟨decodeRow 12 ("27143506", 8), 748⟩])
                  (.leaf [⟨decodeRow 12 ("71435026", 6), 749⟩, ⟨decodeRow 12 ("67143520", 8), 748⟩, ⟨decodeRow 12 ("71435260", 8), 749⟩, ⟨decodeRow 12 ("14352670", 8), 750⟩, ⟨decodeRow 12 ("43526710", 6), 751⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("04352617", 6), 750⟩, ⟨decodeRow 12 ("70435216", 8), 749⟩, ⟨decodeRow 12 ("04352176", 8), 750⟩, ⟨decodeRow 12 ("43521706", 8), 751⟩])
                  (.leaf [⟨decodeRow 12 ("35217046", 8), 752⟩, ⟨decodeRow 12 ("52170436", 6), 753⟩, ⟨decodeRow 12 ("65217034", 8), 752⟩, ⟨decodeRow 12 ("52170364", 8), 753⟩, ⟨decodeRow 12 ("21703654", 8), 754⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("17036524", 6), 755⟩, ⟨decodeRow 12 ("41703625", 8), 754⟩, ⟨decodeRow 12 ("17036245", 8), 755⟩, ⟨decodeRow 12 ("70362415", 8), 756⟩])
                  (.leaf [⟨decodeRow 12 ("03624175", 8), 757⟩, ⟨decodeRow 12 ("36241705", 8), 758⟩, ⟨decodeRow 12 ("62417035", 6), 759⟩, ⟨decodeRow 12 ("56241730", 8), 758⟩, ⟨decodeRow 12 ("62417350", 8), 759⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("24173560", 6), 760⟩, ⟨decodeRow 12 ("02417365", 8), 759⟩, ⟨decodeRow 12 ("24173605", 8), 760⟩, ⟨decodeRow 12 ("41736025", 8), 761⟩])
                  (.leaf [⟨decodeRow 12 ("17360245", 8), 762⟩, ⟨decodeRow 12 ("73602415", 6), 763⟩, ⟨decodeRow 12 ("57360214", 8), 762⟩, ⟨decodeRow 12 ("73602154", 8), 763⟩, ⟨decodeRow 12 ("36021574", 8), 764⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("60215734", 6), 765⟩, ⟨decodeRow 12 ("46021537", 6), 764⟩, ⟨decodeRow 12 ("74602135", 8), 763⟩, ⟨decodeRow 12 ("46021375", 8), 764⟩])
                  (.leaf [⟨decodeRow 12 ("60213745", 8), 765⟩, ⟨decodeRow 12 ("02137465", 8), 766⟩, ⟨decodeRow 12 ("21374605", 8), 767⟩, ⟨decodeRow 12 ("13746025", 6), 768⟩, ⟨decodeRow 12 ("51374620", 8), 767⟩])))))
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("13746250", 8), 768⟩, ⟨decodeRow 12 ("37462510", 8), 769⟩, ⟨decodeRow 12 ("74625130", 6), 770⟩, ⟨decodeRow 12 ("07462531", 8), 769⟩, ⟨decodeRow 12 ("74625301", 8), 770⟩, ⟨decodeRow 12 ("46253071", 8), 771⟩, ⟨decodeRow 12 ("62530741", 8), 772⟩, ⟨decodeRow 12 ("25307461", 6), 773⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("12530764", 8), 772⟩, ⟨decodeRow 12 ("25307614", 8), 773⟩, ⟨decodeRow 12 ("53076124", 6), 774⟩, ⟨decodeRow 12 ("45307621", 8), 773⟩])
                  (.leaf [⟨decodeRow 12 ("53076241", 8), 774⟩, ⟨decodeRow 12 ("30762451", 8), 775⟩, ⟨decodeRow 12 ("07624531", 8), 776⟩, ⟨decodeRow 12 ("76245301", 6), 777⟩, ⟨decodeRow 12 ("17624503", 8), 776⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76245013", 8), 777⟩, ⟨decodeRow 12 ("62450173", 8), 778⟩, ⟨decodeRow 12 ("24501763", 8), 779⟩, ⟨decodeRow 12 ("45017623", 6), 780⟩])
                  (.leaf [⟨decodeRow 12 ("34501726", 8), 779⟩, ⟨decodeRow 12 ("45017236", 8), 780⟩, ⟨decodeRow 12 ("50172346", 8), 781⟩, ⟨decodeRow 12 ("01723456", 6), 782⟩, ⟨decodeRow 12 ("60172354", 8), 781⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("01723564", 8), 782⟩, ⟨decodeRow 12 ("17235604", 6), 783⟩, ⟨decodeRow 12 ("41723506", 8), 782⟩, ⟨decodeRow 12 ("17235046", 8), 783⟩])
                  (.leaf [⟨decodeRow 12 ("72350416", 8), 784⟩, ⟨decodeRow 12 ("23504176", 8), 785⟩, ⟨decodeRow 12 ("35041726", 6), 786⟩, ⟨decodeRow 12 ("63504127", 6), 785⟩, ⟨decodeRow 12 ("76350421", 8), 784⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("63504271", 8), 785⟩, ⟨decodeRow 12 ("35042761", 8), 786⟩, ⟨decodeRow 12 ("50427631", 8), 787⟩, ⟨decodeRow 12 ("04276351", 8), 788⟩])
                  (.leaf [⟨decodeRow 12 ("42763501", 6), 789⟩, ⟨decodeRow 12 ("14276305", 8), 788⟩, ⟨decodeRow 12 ("42763015", 8), 789⟩, ⟨decodeRow 12 ("27630145", 8), 790⟩, ⟨decodeRow 12 ("76301425", 6), 791⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("57630124", 8), 790⟩, ⟨decodeRow 12 ("76301254", 8), 791⟩, ⟨decodeRow 12 ("63012574", 8), 792⟩, ⟨decodeRow 12 ("30125764", 8), 793⟩])
                  (.leaf [⟨decodeRow 12 ("01257634", 6), 794⟩, ⟨decodeRow 12 ("40125736", 8), 793⟩, ⟨decodeRow 12 ("01257346", 8), 794⟩, ⟨decodeRow 12 ("12573406", 8), 795⟩, ⟨decodeRow 12 ("25734016", 6), 796⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("62573410", 8), 795⟩, ⟨decodeRow 12 ("25734160", 8), 796⟩, ⟨decodeRow 12 ("57341620", 8), 797⟩, ⟨decodeRow 12 ("73416250", 6), 798⟩])
                  (.leaf [⟨decodeRow 12 ("07341652", 8), 797⟩, ⟨decodeRow 12 ("73416502", 8), 798⟩, ⟨decodeRow 12 ("34165072", 8), 799⟩, ⟨decodeRow 12 ("41650732", 8), 800⟩, ⟨decodeRow 12 ("16507342", 6), 801⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("21650743", 8), 800⟩, ⟨decodeRow 12 ("16507423", 8), 801⟩, ⟨decodeRow 12 ("65074213", 6), 802⟩, ⟨decodeRow 12 ("36507412", 8), 801⟩])
                  (.leaf [⟨decodeRow 12 ("65074132", 8), 802⟩, ⟨decodeRow 12 ("50741362", 8), 803⟩, ⟨decodeRow 12 ("07413652", 6), 804⟩, ⟨decodeRow 12 ("20741356", 8), 803⟩, ⟨decodeRow 12 ("07413526", 8), 804⟩]))))))
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("74135206", 8), 805⟩, ⟨decodeRow 12 ("41352076", 8), 806⟩, ⟨decodeRow 12 ("13520746", 8), 807⟩, ⟨decodeRow 12 ("35207416", 6), 808⟩, ⟨decodeRow 12 ("63520714", 8), 807⟩, ⟨decodeRow 12 ("35207164", 8), 808⟩, ⟨decodeRow 12 ("52071634", 8), 809⟩, ⟨decodeRow 12 ("20716354", 6), 810⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("42071653", 8), 809⟩, ⟨decodeRow 12 ("20716543", 8), 810⟩, ⟨decodeRow 12 ("07165423", 8), 811⟩, ⟨decodeRow 12 ("71654203", 6), 812⟩])
                  (.leaf [⟨decodeRow 12 ("37165402", 8), 811⟩, ⟨decodeRow 12 ("71654032", 8), 812⟩, ⟨decodeRow 12 ("16540372", 8), 813⟩, ⟨decodeRow 12 ("65403712", 8), 814⟩, ⟨decodeRow 12 ("54037162", 6), 815⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("25403761", 8), 814⟩, ⟨decodeRow 12 ("54037621", 8), 815⟩, ⟨decodeRow 12 ("40376251", 6), 816⟩, ⟨decodeRow 12 ("14037652", 8), 815⟩])
                  (.leaf [⟨decodeRow 12 ("40376512", 8), 816⟩, ⟨decodeRow 12 ("03765142", 8), 817⟩, ⟨decodeRow 12 ("37651402", 8), 818⟩, ⟨decodeRow 12 ("76514032", 6), 819⟩, ⟨decodeRow 12 ("27651430", 8), 818⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("76514320", 8), 819⟩, ⟨decodeRow 12 ("65143270", 8), 820⟩, ⟨decodeRow 12 ("51432760", 8), 821⟩, ⟨decodeRow 12 ("14327650", 6), 822⟩])
                  (.leaf [⟨decodeRow 12 ("01432756", 8), 821⟩, ⟨decodeRow 12 ("14327506", 8), 822⟩, ⟨decodeRow 12 ("43275016", 8), 823⟩, ⟨decodeRow 12 ("32750146", 6), 824⟩, ⟨decodeRow 12 ("63275041", 8), 823⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("32750461", 8), 824⟩, ⟨decodeRow 12 ("27504631", 8), 825⟩, ⟨decodeRow 12 ("75046321", 6), 826⟩, ⟨decodeRow 12 ("17504623", 8), 825⟩])
                  (.leaf [⟨decodeRow 12 ("75046213", 8), 826⟩, ⟨decodeRow 12 ("50462173", 8), 827⟩, ⟨decodeRow 12 ("04621753", 8), 828⟩, ⟨decodeRow 12 ("46217503", 6), 829⟩, ⟨decodeRow 12 ("34621705", 8), 828⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("46217035", 8), 829⟩, ⟨decodeRow 12 ("62170345", 6), 830⟩, ⟨decodeRow 12 ("56217043", 8), 829⟩, ⟨decodeRow 12 ("62170453", 8), 830⟩])
                  (.leaf [⟨decodeRow 12 ("21704563", 8), 831⟩, ⟨decodeRow 12 ("17045623", 6), 832⟩, ⟨decodeRow 12 ("31704526", 8), 831⟩, ⟨decodeRow 12 ("17045236", 8), 832⟩, ⟨decodeRow 12 ("70452316", 8), 833⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("04523176", 8), 834⟩, ⟨decodeRow 12 ("45231706", 8), 835⟩, ⟨decodeRow 12 ("52317046", 6), 836⟩, ⟨decodeRow 12 ("65231740", 8), 835⟩])
                  (.leaf [⟨decodeRow 12 ("52317460", 8), 836⟩, ⟨decodeRow 12 ("23174650", 8), 837⟩, ⟨decodeRow 12 ("31746520", 6), 838⟩, ⟨decodeRow 12 ("03174625", 8), 837⟩, ⟨decodeRow 12 ("31746205", 8), 838⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("17462035", 8), 839⟩, ⟨decodeRow 12 ("74620315", 6), 840⟩, ⟨decodeRow 12 ("57462013", 8), 839⟩, ⟨decodeRow 12 ("74620153", 8), 840⟩])
                  (.leaf [⟨decodeRow 12 ("46201573", 8), 841⟩, ⟨decodeRow 12 ("62015743", 8), 842⟩, ⟨decodeRow 12 ("20157463", 6), 843⟩, ⟨decodeRow 12 ("32015764", 8), 842⟩, ⟨decodeRow 12 ("20157634", 8), 843⟩])))))
          (.branch 36
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("01576324", 6), 844⟩, ⟨decodeRow 12 ("40157623", 8), 843⟩, ⟨decodeRow 12 ("01576243", 8), 844⟩, ⟨decodeRow 12 ("15762403", 8), 845⟩])
                  (.leaf [⟨decodeRow 12 ("57624013", 8), 846⟩, ⟨decodeRow 12 ("76240153", 6), 847⟩, ⟨decodeRow 12 ("37624051", 8), 846⟩, ⟨decodeRow 12 ("76240531", 8), 847⟩, ⟨decodeRow 12 ("62405371", 8), 848⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("24053761", 8), 849⟩, ⟨decodeRow 12 ("40537621", 6), 850⟩, ⟨decodeRow 12 ("14053726", 8), 849⟩, ⟨decodeRow 12 ("40537216", 8), 850⟩])
                  (.leaf [⟨decodeRow 12 ("05372146", 8), 851⟩, ⟨decodeRow 12 ("53721406", 6), 852⟩, ⟨decodeRow 12 ("65372104", 8), 851⟩, ⟨decodeRow 12 ("53721064", 8), 852⟩, ⟨decodeRow 12 ("37210654", 8), 853⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("72106534", 6), 854⟩, ⟨decodeRow 12 ("47210635", 8), 853⟩, ⟨decodeRow 12 ("72106345", 8), 854⟩, ⟨decodeRow 12 ("21063475", 8), 855⟩])
                  (.leaf [⟨decodeRow 12 ("10634725", 8), 856⟩, ⟨decodeRow 12 ("06347215", 6), 857⟩, ⟨decodeRow 12 ("50634712", 8), 856⟩, ⟨decodeRow 12 ("06347152", 8), 857⟩, ⟨decodeRow 12 ("63471502", 6), 858⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("26347105", 8), 857⟩, ⟨decodeRow 12 ("63471025", 8), 858⟩, ⟨decodeRow 12 ("34710265", 8), 859⟩, ⟨decodeRow 12 ("47102635", 6), 860⟩])
                  (.leaf [⟨decodeRow 12 ("54710236", 8), 859⟩, ⟨decodeRow 12 ("47102356", 8), 860⟩, ⟨decodeRow 12 ("71023546", 8), 861⟩, ⟨decodeRow 12 ("10235476", 8), 862⟩, ⟨decodeRow 12 ("02354716", 8), 863⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("23547106", 6), 864⟩, ⟨decodeRow 12 ("62354701", 8), 863⟩, ⟨decodeRow 12 ("23547061", 8), 864⟩, ⟨decodeRow 12 ("35470621", 8), 865⟩])
                  (.leaf [⟨decodeRow 12 ("54706231", 6), 866⟩, ⟨decodeRow 12 ("15470632", 8), 865⟩, ⟨decodeRow 12 ("54706312", 8), 866⟩, ⟨decodeRow 12 ("47063152", 8), 867⟩, ⟨decodeRow 12 ("70631542", 6), 868⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27063145", 8), 867⟩, ⟨decodeRow 12 ("70631425", 8), 868⟩, ⟨decodeRow 12 ("06314275", 8), 869⟩, ⟨decodeRow 12 ("63142705", 8), 870⟩])
                  (.leaf [⟨decodeRow 12 ("31427065", 6), 871⟩, ⟨decodeRow 12 ("53142760", 8), 870⟩, ⟨decodeRow 12 ("31427650", 8), 871⟩, ⟨decodeRow 12 ("14276530", 8), 872⟩, ⟨decodeRow 12 ("42765310", 6), 873⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("04276513", 8), 872⟩, ⟨decodeRow 12 ("42765103", 8), 873⟩, ⟨decodeRow 12 ("27651043", 8), 874⟩, ⟨decodeRow 12 ("76510423", 6), 875⟩])
                  (.leaf [⟨decodeRow 12 ("37651024", 8), 874⟩, ⟨decodeRow 12 ("76510234", 8), 875⟩, ⟨decodeRow 12 ("65102374", 8), 876⟩, ⟨decodeRow 12 ("51023764", 6), 877⟩, ⟨decodeRow 12 ("45102367", 6), 876⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74510263", 8), 875⟩, ⟨decodeRow 12 ("45102673", 8), 876⟩, ⟨decodeRow 12 ("51026743", 8), 877⟩, ⟨decodeRow 12 ("10267453", 8), 878⟩])
                  (.leaf [⟨decodeRow 12 ("02674513", 6), 879⟩, ⟨decodeRow 12 ("30267415", 8), 878⟩, ⟨decodeRow 12 ("02674135", 8), 879⟩, ⟨decodeRow 12 ("26741305", 8), 880⟩, ⟨decodeRow 12 ("67413025", 8), 881⟩]))))))))
    (.branch 285
      (.branch 142
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("74130265", 6), 882⟩, ⟨decodeRow 12 ("57413062", 8), 881⟩, ⟨decodeRow 12 ("74130652", 8), 882⟩, ⟨decodeRow 12 ("41306572", 8), 883⟩, ⟨decodeRow 12 ("13065742", 8), 884⟩, ⟨decodeRow 12 ("30657412", 6), 885⟩, ⟨decodeRow 12 ("23065714", 8), 884⟩, ⟨decodeRow 12 ("30657124", 8), 885⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("06571234", 8), 886⟩, ⟨decodeRow 12 ("65712304", 6), 887⟩, ⟨decodeRow 12 ("46571203", 8), 886⟩, ⟨decodeRow 12 ("65712043", 8), 887⟩])
                  (.leaf [⟨decodeRow 12 ("57120463", 8), 888⟩, ⟨decodeRow 12 ("71204653", 6), 889⟩, ⟨decodeRow 12 ("37120456", 8), 888⟩, ⟨decodeRow 12 ("71204536", 8), 889⟩, ⟨decodeRow 12 ("12045376", 8), 890⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("20453716", 8), 891⟩, ⟨decodeRow 12 ("04537126", 6), 892⟩, ⟨decodeRow 12 ("60453721", 8), 891⟩, ⟨decodeRow 12 ("04537261", 8), 892⟩])
                  (.leaf [⟨decodeRow 12 ("45372601", 8), 893⟩, ⟨decodeRow 12 ("53726041", 6), 894⟩, ⟨decodeRow 12 ("15372640", 8), 893⟩, ⟨decodeRow 12 ("53726410", 8), 894⟩, ⟨decodeRow 12 ("37264150", 6), 895⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03726451", 8), 894⟩, ⟨decodeRow 12 ("37264501", 8), 895⟩, ⟨decodeRow 12 ("72645031", 8), 896⟩, ⟨decodeRow 12 ("26450371", 8), 897⟩])
                  (.leaf [⟨decodeRow 12 ("64503721", 6), 898⟩, ⟨decodeRow 12 ("16450327", 6), 897⟩, ⟨decodeRow 12 ("71645023", 8), 896⟩, ⟨decodeRow 12 ("16450273", 8), 897⟩, ⟨decodeRow 12 ("64502713", 8), 898⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45027163", 8), 899⟩, ⟨decodeRow 12 ("50271643", 8), 900⟩, ⟨decodeRow 12 ("02716453", 6), 901⟩, ⟨decodeRow 12 ("30271654", 8), 900⟩])
                  (.leaf [⟨decodeRow 12 ("02716534", 8), 901⟩, ⟨decodeRow 12 ("27165304", 8), 902⟩, ⟨decodeRow 12 ("71653024", 6), 903⟩, ⟨decodeRow 12 ("47165320", 8), 902⟩, ⟨decodeRow 12 ("71653240", 8), 903⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("16532470", 8), 904⟩, ⟨decodeRow 12 ("65324710", 8), 905⟩, ⟨decodeRow 12 ("53247160", 6), 906⟩, ⟨decodeRow 12 ("05324761", 8), 905⟩])
                  (.leaf [⟨decodeRow 12 ("53247601", 8), 906⟩, ⟨decodeRow 12 ("32476051", 8), 907⟩, ⟨decodeRow 12 ("24760531", 6), 908⟩, ⟨decodeRow 12 ("12476035", 8), 907⟩, ⟨decodeRow 12 ("24760315", 8), 908⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47603125", 8), 909⟩, ⟨decodeRow 12 ("76031245", 6), 910⟩, ⟨decodeRow 12 ("57603142", 8), 909⟩, ⟨decodeRow 12 ("76031452", 8), 910⟩])
                  (.leaf [⟨decodeRow 12 ("60314572", 8), 911⟩, ⟨decodeRow 12 ("03145762", 8), 912⟩, ⟨decodeRow 12 ("31457602", 6), 913⟩, ⟨decodeRow 12 ("23145706", 8), 912⟩, ⟨decodeRow 12 ("31457026", 8), 913⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("14570236", 6), 914⟩, ⟨decodeRow 12 ("61457032", 8), 913⟩, ⟨decodeRow 12 ("14570362", 8), 914⟩, ⟨decodeRow 12 ("45703612", 8), 915⟩])
                  (.leaf [⟨decodeRow 12 ("57036142", 6), 916⟩, ⟨decodeRow 12 ("25703641", 8), 915⟩, ⟨decodeRow 12 ("57036421", 8), 916⟩, ⟨decodeRow 12 ("70364251", 8), 917⟩, ⟨decodeRow 12 ("03642571", 8), 918⟩])))))
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("36425701", 8), 919⟩, ⟨decodeRow 12 ("64257031", 6), 920⟩, ⟨decodeRow 12 ("16425730", 8), 919⟩, ⟨decodeRow 12 ("64257310", 8), 920⟩, ⟨decodeRow 12 ("42573160", 8), 921⟩, ⟨decodeRow 12 ("25731640", 6), 922⟩, ⟨decodeRow 12 ("02573146", 8), 921⟩, ⟨decodeRow 12 ("25731406", 8), 922⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("57314026", 6), 923⟩, ⟨decodeRow 12 ("65731420", 8), 922⟩, ⟨decodeRow 12 ("57314260", 8), 923⟩, ⟨decodeRow 12 ("73142650", 8), 924⟩])
                  (.leaf [⟨decodeRow 12 ("31426570", 8), 925⟩, ⟨decodeRow 12 ("14265730", 8), 926⟩, ⟨decodeRow 12 ("42657310", 6), 927⟩, ⟨decodeRow 12 ("04265713", 8), 926⟩, ⟨decodeRow 12 ("42657103", 8), 927⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("26571043", 6), 928⟩, ⟨decodeRow 12 ("32657140", 8), 927⟩, ⟨decodeRow 12 ("26571430", 8), 928⟩, ⟨decodeRow 12 ("65714320", 8), 929⟩])
                  (.leaf [⟨decodeRow 12 ("57143260", 8), 930⟩, ⟨decodeRow 12 ("71432650", 6), 931⟩, ⟨decodeRow 12 ("07143256", 8), 930⟩, ⟨decodeRow 12 ("71432506", 8), 931⟩, ⟨decodeRow 12 ("14325076", 8), 932⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("43250716", 8), 933⟩, ⟨decodeRow 12 ("32507146", 6), 934⟩, ⟨decodeRow 12 ("63250741", 8), 933⟩, ⟨decodeRow 12 ("32507461", 8), 934⟩])
                  (.leaf [⟨decodeRow 12 ("25074631", 8), 935⟩, ⟨decodeRow 12 ("50746321", 6), 936⟩, ⟨decodeRow 12 ("15074623", 8), 935⟩, ⟨decodeRow 12 ("50746213", 8), 936⟩, ⟨decodeRow 12 ("07462153", 8), 937⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74621503", 6), 938⟩, ⟨decodeRow 12 ("37462105", 8), 937⟩, ⟨decodeRow 12 ("74621035", 8), 938⟩, ⟨decodeRow 12 ("46210375", 8), 939⟩])
                  (.leaf [⟨decodeRow 12 ("62103745", 6), 940⟩, ⟨decodeRow 12 ("56210347", 6), 939⟩, ⟨decodeRow 12 ("75621043", 8), 938⟩, ⟨decodeRow 12 ("56210473", 8), 939⟩, ⟨decodeRow 12 ("62104753", 8), 940⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("21047563", 8), 941⟩, ⟨decodeRow 12 ("10475623", 6), 942⟩, ⟨decodeRow 12 ("31047526", 8), 941⟩, ⟨decodeRow 12 ("10475236", 8), 942⟩])
                  (.leaf [⟨decodeRow 12 ("04752316", 8), 943⟩, ⟨decodeRow 12 ("47523106", 8), 944⟩, ⟨decodeRow 12 ("75231046", 6), 945⟩, ⟨decodeRow 12 ("67523140", 8), 944⟩, ⟨decodeRow 12 ("75231460", 8), 945⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("52314670", 8), 946⟩, ⟨decodeRow 12 ("23146750", 8), 947⟩, ⟨decodeRow 12 ("31467520", 6), 948⟩, ⟨decodeRow 12 ("03146725", 8), 947⟩])
                  (.leaf [⟨decodeRow 12 ("31467205", 8), 948⟩, ⟨decodeRow 12 ("14672035", 8), 949⟩, ⟨decodeRow 12 ("46720315", 6), 950⟩, ⟨decodeRow 12 ("54672013", 8), 949⟩, ⟨decodeRow 12 ("46720153", 8), 950⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67201543", 8), 951⟩, ⟨decodeRow 12 ("72015463", 6), 952⟩, ⟨decodeRow 12 ("37201564", 8), 951⟩, ⟨decodeRow 12 ("72015634", 8), 952⟩])
                  (.leaf [⟨decodeRow 12 ("20156374", 8), 953⟩, ⟨decodeRow 12 ("01563724", 6), 954⟩, ⟨decodeRow 12 ("40156327", 6), 953⟩, ⟨decodeRow 12 ("74015623", 8), 952⟩, ⟨decodeRow 12 ("40156273", 8), 953⟩]))))))
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("01562743", 8), 954⟩, ⟨decodeRow 12 ("15627403", 8), 955⟩, ⟨decodeRow 12 ("56274013", 8), 956⟩, ⟨decodeRow 12 ("62740153", 6), 957⟩, ⟨decodeRow 12 ("36274051", 8), 956⟩, ⟨decodeRow 12 ("62740531", 8), 957⟩, ⟨decodeRow 12 ("27405361", 8), 958⟩, ⟨decodeRow 12 ("74053621", 6), 959⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("17405326", 8), 958⟩, ⟨decodeRow 12 ("74053216", 8), 959⟩, ⟨decodeRow 12 ("40532176", 8), 960⟩, ⟨decodeRow 12 ("05321746", 8), 961⟩])
                  (.leaf [⟨decodeRow 12 ("53217406", 6), 962⟩, ⟨decodeRow 12 ("65321704", 8), 961⟩, ⟨decodeRow 12 ("53217064", 8), 962⟩, ⟨decodeRow 12 ("32170654", 8), 963⟩, ⟨decodeRow 12 ("21706534", 6), 964⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("42170635", 8), 963⟩, ⟨decodeRow 12 ("21706345", 8), 964⟩, ⟨decodeRow 12 ("17063425", 8), 965⟩, ⟨decodeRow 12 ("70634215", 6), 966⟩])
                  (.leaf [⟨decodeRow 12 ("57063412", 8), 965⟩, ⟨decodeRow 12 ("70634152", 8), 966⟩, ⟨decodeRow 12 ("06341572", 8), 967⟩, ⟨decodeRow 12 ("63415702", 6), 968⟩, ⟨decodeRow 12 ("26341507", 6), 967⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("72634105", 8), 966⟩, ⟨decodeRow 12 ("26341075", 8), 967⟩, ⟨decodeRow 12 ("63410725", 8), 968⟩, ⟨decodeRow 12 ("34107265", 8), 969⟩])
                  (.leaf [⟨decodeRow 12 ("41072635", 6), 970⟩, ⟨decodeRow 12 ("54107236", 8), 969⟩, ⟨decodeRow 12 ("41072356", 8), 970⟩, ⟨decodeRow 12 ("10723546", 8), 971⟩, ⟨decodeRow 12 ("07235416", 8), 972⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("72354106", 6), 973⟩, ⟨decodeRow 12 ("67235401", 8), 972⟩, ⟨decodeRow 12 ("72354061", 8), 973⟩, ⟨decodeRow 12 ("23540671", 8), 974⟩])
                  (.leaf [⟨decodeRow 12 ("35406721", 8), 975⟩, ⟨decodeRow 12 ("54067231", 6), 976⟩, ⟨decodeRow 12 ("15406732", 8), 975⟩, ⟨decodeRow 12 ("54067312", 8), 976⟩, ⟨decodeRow 12 ("40673152", 8), 977⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("06731542", 6), 978⟩, ⟨decodeRow 12 ("20673145", 8), 977⟩, ⟨decodeRow 12 ("06731425", 8), 978⟩, ⟨decodeRow 12 ("67314205", 6), 979⟩])
                  (.leaf [⟨decodeRow 12 ("56731402", 8), 978⟩, ⟨decodeRow 12 ("67314052", 8), 979⟩, ⟨decodeRow 12 ("73140562", 8), 980⟩, ⟨decodeRow 12 ("31405672", 8), 981⟩, ⟨decodeRow 12 ("14056732", 8), 982⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40567312", 6), 983⟩, ⟨decodeRow 12 ("24056713", 8), 982⟩, ⟨decodeRow 12 ("40567123", 8), 983⟩, ⟨decodeRow 12 ("05671243", 8), 984⟩])
                  (.leaf [⟨decodeRow 12 ("56712403", 6), 985⟩, ⟨decodeRow 12 ("35671204", 8), 984⟩, ⟨decodeRow 12 ("56712034", 8), 985⟩, ⟨decodeRow 12 ("67120354", 8), 986⟩, ⟨decodeRow 12 ("71203564", 6), 987⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("47120365", 8), 986⟩, ⟨decodeRow 12 ("71203645", 8), 987⟩, ⟨decodeRow 12 ("12036475", 8), 988⟩, ⟨decodeRow 12 ("20364715", 6), 989⟩])
                  (.leaf [⟨decodeRow 12 ("52036417", 6), 988⟩, ⟨decodeRow 12 ("75203614", 8), 987⟩, ⟨decodeRow 12 ("52036174", 8), 988⟩, ⟨decodeRow 12 ("20361754", 8), 989⟩, ⟨decodeRow 12 ("03617524", 8), 990⟩])))))
          (.branch 36
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("36175204", 6), 991⟩, ⟨decodeRow 12 ("43617502", 8), 990⟩, ⟨decodeRow 12 ("36175042", 8), 991⟩, ⟨decodeRow 12 ("61750432", 8), 992⟩])
                  (.leaf [⟨decodeRow 12 ("17504362", 8), 993⟩, ⟨decodeRow 12 ("75043612", 6), 994⟩, ⟨decodeRow 12 ("27504316", 8), 993⟩, ⟨decodeRow 12 ("75043126", 8), 994⟩, ⟨decodeRow 12 ("50431276", 8), 995⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("04312756", 8), 996⟩, ⟨decodeRow 12 ("43127506", 6), 997⟩, ⟨decodeRow 12 ("64312705", 8), 996⟩, ⟨decodeRow 12 ("43127065", 8), 997⟩])
                  (.leaf [⟨decodeRow 12 ("31270645", 8), 998⟩, ⟨decodeRow 12 ("12706435", 6), 999⟩, ⟨decodeRow 12 ("51270634", 8), 998⟩, ⟨decodeRow 12 ("12706354", 8), 999⟩, ⟨decodeRow 12 ("27063514", 8), 1000⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("70635124", 6), 1001⟩, ⟨decodeRow 12 ("47063521", 8), 1000⟩, ⟨decodeRow 12 ("70635241", 8), 1001⟩, ⟨decodeRow 12 ("06352471", 8), 1002⟩])
                  (.leaf [⟨decodeRow 12 ("63524701", 8), 1003⟩, ⟨decodeRow 12 ("35247061", 6), 1004⟩, ⟨decodeRow 12 ("13524760", 8), 1003⟩, ⟨decodeRow 12 ("35247610", 8), 1004⟩, ⟨decodeRow 12 ("52476130", 8), 1005⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("24761350", 6), 1006⟩, ⟨decodeRow 12 ("02476153", 8), 1005⟩, ⟨decodeRow 12 ("24761503", 8), 1006⟩, ⟨decodeRow 12 ("47615023", 6), 1007⟩])
                  (.leaf [⟨decodeRow 12 ("34761520", 8), 1006⟩, ⟨decodeRow 12 ("47615230", 8), 1007⟩, ⟨decodeRow 12 ("76152340", 8), 1008⟩, ⟨decodeRow 12 ("61523470", 8), 1009⟩, ⟨decodeRow 12 ("15234760", 6), 1010⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("01523467", 6), 1009⟩, ⟨decodeRow 12 ("70152364", 8), 1008⟩, ⟨decodeRow 12 ("01523674", 8), 1009⟩, ⟨decodeRow 12 ("15236704", 8), 1010⟩])
                  (.leaf [⟨decodeRow 12 ("52367014", 8), 1011⟩, ⟨decodeRow 12 ("23670154", 8), 1012⟩, ⟨decodeRow 12 ("36701524", 6), 1013⟩, ⟨decodeRow 12 ("43670125", 8), 1012⟩, ⟨decodeRow 12 ("36701245", 8), 1013⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67012435", 8), 1014⟩, ⟨decodeRow 12 ("70124365", 6), 1015⟩, ⟨decodeRow 12 ("57012463", 8), 1014⟩, ⟨decodeRow 12 ("70124653", 8), 1015⟩])
                  (.leaf [⟨decodeRow 12 ("01246573", 8), 1016⟩, ⟨decodeRow 12 ("12465703", 8), 1017⟩, ⟨decodeRow 12 ("24657013", 6), 1018⟩, ⟨decodeRow 12 ("32465710", 8), 1017⟩, ⟨decodeRow 12 ("24657130", 8), 1018⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("46571320", 8), 1019⟩, ⟨decodeRow 12 ("65713240", 6), 1020⟩, ⟨decodeRow 12 ("06571342", 8), 1019⟩, ⟨decodeRow 12 ("65713402", 8), 1020⟩])
                  (.leaf [⟨decodeRow 12 ("57134062", 8), 1021⟩, ⟨decodeRow 12 ("71340652", 6), 1022⟩, ⟨decodeRow 12 ("27134056", 8), 1021⟩, ⟨decodeRow 12 ("71340526", 8), 1022⟩, ⟨decodeRow 12 ("13405276", 8), 1023⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("34052716", 8), 1024⟩, ⟨decodeRow 12 ("40527136", 6), 1025⟩, ⟨decodeRow 12 ("64052731", 8), 1024⟩, ⟨decodeRow 12 ("40527361", 8), 1025⟩])
                  (.leaf [⟨decodeRow 12 ("05273641", 6), 1026⟩, ⟨decodeRow 12 ("10527346", 8), 1025⟩, ⟨decodeRow 12 ("05273416", 8), 1026⟩, ⟨decodeRow 12 ("52734106", 8), 1027⟩, ⟨decodeRow 12 ("27341056", 6), 1028⟩])))))))
      (.branch 142
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("62734150", 8), 1027⟩, ⟨decodeRow 12 ("27341560", 8), 1028⟩, ⟨decodeRow 12 ("73415620", 8), 1029⟩, ⟨decodeRow 12 ("34156270", 8), 1030⟩, ⟨decodeRow 12 ("41562730", 6), 1031⟩, ⟨decodeRow 12 ("04156237", 6), 1030⟩, ⟨decodeRow 12 ("70415632", 8), 1029⟩, ⟨decodeRow 12 ("04156372", 8), 1030⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("41563702", 8), 1031⟩, ⟨decodeRow 12 ("15637042", 8), 1032⟩, ⟨decodeRow 12 ("56370412", 8), 1033⟩, ⟨decodeRow 12 ("63704152", 6), 1034⟩])
                  (.leaf [⟨decodeRow 12 ("26370451", 8), 1033⟩, ⟨decodeRow 12 ("63704521", 8), 1034⟩, ⟨decodeRow 12 ("37045261", 6), 1035⟩, ⟨decodeRow 12 ("13704562", 8), 1034⟩, ⟨decodeRow 12 ("37045612", 8), 1035⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("70456132", 8), 1036⟩, ⟨decodeRow 12 ("04561372", 8), 1037⟩, ⟨decodeRow 12 ("45613702", 6), 1038⟩, ⟨decodeRow 12 ("24561307", 6), 1037⟩])
                  (.leaf [⟨decodeRow 12 ("72456103", 8), 1036⟩, ⟨decodeRow 12 ("24561073", 8), 1037⟩, ⟨decodeRow 12 ("45610723", 8), 1038⟩, ⟨decodeRow 12 ("56107243", 8), 1039⟩, ⟨decodeRow 12 ("61072453", 6), 1040⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("36107254", 8), 1039⟩, ⟨decodeRow 12 ("61072534", 8), 1040⟩, ⟨decodeRow 12 ("10725364", 8), 1041⟩, ⟨decodeRow 12 ("07253614", 8), 1042⟩])
                  (.leaf [⟨decodeRow 12 ("72536104", 6), 1043⟩, ⟨decodeRow 12 ("47253601", 8), 1042⟩, ⟨decodeRow 12 ("72536041", 8), 1043⟩, ⟨decodeRow 12 ("25360471", 8), 1044⟩, ⟨decodeRow 12 ("53604721", 8), 1045⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("36047251", 6), 1046⟩, ⟨decodeRow 12 ("13604752", 8), 1045⟩, ⟨decodeRow 12 ("36047512", 8), 1046⟩, ⟨decodeRow 12 ("60475132", 8), 1047⟩])
                  (.leaf [⟨decodeRow 12 ("04751362", 6), 1048⟩, ⟨decodeRow 12 ("20475163", 8), 1047⟩, ⟨decodeRow 12 ("04751623", 8), 1048⟩, ⟨decodeRow 12 ("47516203", 8), 1049⟩, ⟨decodeRow 12 ("75162043", 6), 1050⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("37516240", 8), 1049⟩, ⟨decodeRow 12 ("75162430", 8), 1050⟩, ⟨decodeRow 12 ("51624370", 8), 1051⟩, ⟨decodeRow 12 ("16243750", 8), 1052⟩])
                  (.leaf [⟨decodeRow 12 ("62437510", 6), 1053⟩, ⟨decodeRow 12 ("06243715", 8), 1052⟩, ⟨decodeRow 12 ("62437105", 8), 1053⟩, ⟨decodeRow 12 ("24371065", 8), 1054⟩, ⟨decodeRow 12 ("43710625", 6), 1055⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("54371026", 8), 1054⟩, ⟨decodeRow 12 ("43710256", 8), 1055⟩, ⟨decodeRow 12 ("37102546", 6), 1056⟩, ⟨decodeRow 12 ("63710245", 8), 1055⟩])
                  (.leaf [⟨decodeRow 12 ("37102465", 8), 1056⟩, ⟨decodeRow 12 ("71024635", 8), 1057⟩, ⟨decodeRow 12 ("10246375", 8), 1058⟩, ⟨decodeRow 12 ("02463715", 8), 1059⟩, ⟨decodeRow 12 ("24637105", 6), 1060⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("52463701", 8), 1059⟩, ⟨decodeRow 12 ("24637051", 8), 1060⟩, ⟨decodeRow 12 ("46370521", 8), 1061⟩, ⟨decodeRow 12 ("63705241", 6), 1062⟩])
                  (.leaf [⟨decodeRow 12 ("16370542", 8), 1061⟩, ⟨decodeRow 12 ("63705412", 8), 1062⟩, ⟨decodeRow 12 ("37054162", 8), 1063⟩, ⟨decodeRow 12 ("70541632", 6), 1064⟩, ⟨decodeRow 12 ("27054136", 8), 1063⟩])))))
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("70541326", 8), 1064⟩, ⟨decodeRow 12 ("05413276", 8), 1065⟩, ⟨decodeRow 12 ("54132706", 8), 1066⟩, ⟨decodeRow 12 ("41327056", 6), 1067⟩, ⟨decodeRow 12 ("64132750", 8), 1066⟩, ⟨decodeRow 12 ("41327560", 8), 1067⟩, ⟨decodeRow 12 ("13275640", 8), 1068⟩, ⟨decodeRow 12 ("32756410", 6), 1069⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03275614", 8), 1068⟩, ⟨decodeRow 12 ("32756104", 8), 1069⟩, ⟨decodeRow 12 ("27561034", 6), 1070⟩, ⟨decodeRow 12 ("42756130", 8), 1069⟩])
                  (.leaf [⟨decodeRow 12 ("27561340", 8), 1070⟩, ⟨decodeRow 12 ("75613420", 8), 1071⟩, ⟨decodeRow 12 ("56134270", 8), 1072⟩, ⟨decodeRow 12 ("61342750", 6), 1073⟩, ⟨decodeRow 12 ("06134257", 6), 1072⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("70613452", 8), 1071⟩, ⟨decodeRow 12 ("06134572", 8), 1072⟩, ⟨decodeRow 12 ("61345702", 8), 1073⟩, ⟨decodeRow 12 ("13457062", 8), 1074⟩])
                  (.leaf [⟨decodeRow 12 ("34570612", 8), 1075⟩, ⟨decodeRow 12 ("45706132", 6), 1076⟩, ⟨decodeRow 12 ("24570631", 8), 1075⟩, ⟨decodeRow 12 ("45706321", 8), 1076⟩, ⟨decodeRow 12 ("57063241", 8), 1077⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("70632451", 6), 1078⟩, ⟨decodeRow 12 ("17063254", 8), 1077⟩, ⟨decodeRow 12 ("70632514", 8), 1078⟩, ⟨decodeRow 12 ("06325174", 8), 1079⟩])
                  (.leaf [⟨decodeRow 12 ("63251704", 8), 1080⟩, ⟨decodeRow 12 ("32517064", 6), 1081⟩, ⟨decodeRow 12 ("43251760", 8), 1080⟩, ⟨decodeRow 12 ("32517640", 8), 1081⟩, ⟨decodeRow 12 ("25176430", 8), 1082⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("51764320", 6), 1083⟩, ⟨decodeRow 12 ("05176423", 8), 1082⟩, ⟨decodeRow 12 ("51764203", 8), 1083⟩, ⟨decodeRow 12 ("17642053", 8), 1084⟩])
                  (.leaf [⟨decodeRow 12 ("76420513", 6), 1085⟩, ⟨decodeRow 12 ("37642015", 8), 1084⟩, ⟨decodeRow 12 ("76420135", 8), 1085⟩, ⟨decodeRow 12 ("64201375", 8), 1086⟩, ⟨decodeRow 12 ("42013765", 8), 1087⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("20137645", 6), 1088⟩, ⟨decodeRow 12 ("52013746", 8), 1087⟩, ⟨decodeRow 12 ("20137456", 8), 1088⟩, ⟨decodeRow 12 ("01374526", 6), 1089⟩])
                  (.leaf [⟨decodeRow 12 ("60137425", 8), 1088⟩, ⟨decodeRow 12 ("01374265", 8), 1089⟩, ⟨decodeRow 12 ("13742605", 8), 1090⟩, ⟨decodeRow 12 ("37426015", 6), 1091⟩, ⟨decodeRow 12 ("53742610", 8), 1090⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("37426150", 8), 1091⟩, ⟨decodeRow 12 ("74261530", 8), 1092⟩, ⟨decodeRow 12 ("42615370", 8), 1093⟩, ⟨decodeRow 12 ("26153740", 8), 1094⟩])
                  (.leaf [⟨decodeRow 12 ("61537420", 6), 1095⟩, ⟨decodeRow 12 ("06153724", 8), 1094⟩, ⟨decodeRow 12 ("61537204", 8), 1095⟩, ⟨decodeRow 12 ("15372064", 8), 1096⟩, ⟨decodeRow 12 ("53720614", 6), 1097⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("45372016", 8), 1096⟩, ⟨decodeRow 12 ("53720146", 8), 1097⟩, ⟨decodeRow 12 ("37201456", 8), 1098⟩, ⟨decodeRow 12 ("72014536", 6), 1099⟩])
                  (.leaf [⟨decodeRow 12 ("67201435", 8), 1098⟩, ⟨decodeRow 12 ("72014365", 8), 1099⟩, ⟨decodeRow 12 ("20143675", 8), 1100⟩, ⟨decodeRow 12 ("01436725", 8), 1101⟩, ⟨decodeRow 12 ("14367205", 6), 1102⟩]))))))
        (.branch 71
          (.branch 35
            (.branch 17
              (.branch 8
                (.leaf [⟨decodeRow 12 ("51436702", 8), 1101⟩, ⟨decodeRow 12 ("14367052", 8), 1102⟩, ⟨decodeRow 12 ("43670512", 8), 1103⟩, ⟨decodeRow 12 ("36705142", 6), 1104⟩, ⟨decodeRow 12 ("23670541", 8), 1103⟩, ⟨decodeRow 12 ("36705421", 8), 1104⟩, ⟨decodeRow 12 ("67054231", 8), 1105⟩, ⟨decodeRow 12 ("70542361", 6), 1106⟩])
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("17054263", 8), 1105⟩, ⟨decodeRow 12 ("70542613", 8), 1106⟩, ⟨decodeRow 12 ("05426173", 8), 1107⟩, ⟨decodeRow 12 ("54261703", 6), 1108⟩])
                  (.leaf [⟨decodeRow 12 ("35426107", 6), 1107⟩, ⟨decodeRow 12 ("73542601", 8), 1106⟩, ⟨decodeRow 12 ("35426071", 8), 1107⟩, ⟨decodeRow 12 ("54260731", 8), 1108⟩, ⟨decodeRow 12 ("42607351", 8), 1109⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("26073541", 6), 1110⟩, ⟨decodeRow 12 ("12607345", 8), 1109⟩, ⟨decodeRow 12 ("26073415", 8), 1110⟩, ⟨decodeRow 12 ("60734125", 8), 1111⟩])
                  (.leaf [⟨decodeRow 12 ("07341265", 8), 1112⟩, ⟨decodeRow 12 ("73412605", 6), 1113⟩, ⟨decodeRow 12 ("57341206", 8), 1112⟩, ⟨decodeRow 12 ("73412056", 8), 1113⟩, ⟨decodeRow 12 ("34120576", 8), 1114⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("41205736", 8), 1115⟩, ⟨decodeRow 12 ("12057346", 6), 1116⟩, ⟨decodeRow 12 ("61205743", 8), 1115⟩, ⟨decodeRow 12 ("12057463", 8), 1116⟩])
                  (.leaf [⟨decodeRow 12 ("20574613", 8), 1117⟩, ⟨decodeRow 12 ("05746123", 6), 1118⟩, ⟨decodeRow 12 ("30574621", 8), 1117⟩, ⟨decodeRow 12 ("05746231", 8), 1118⟩, ⟨decodeRow 12 ("57462301", 8), 1119⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("74623051", 6), 1120⟩, ⟨decodeRow 12 ("17462350", 8), 1119⟩, ⟨decodeRow 12 ("74623510", 8), 1120⟩, ⟨decodeRow 12 ("46235170", 8), 1121⟩])
                  (.leaf [⟨decodeRow 12 ("62351740", 8), 1122⟩, ⟨decodeRow 12 ("23517460", 6), 1123⟩, ⟨decodeRow 12 ("02351764", 8), 1122⟩, ⟨decodeRow 12 ("23517604", 8), 1123⟩, ⟨decodeRow 12 ("35176024", 8), 1124⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("51760234", 6), 1125⟩, ⟨decodeRow 12 ("45176032", 8), 1124⟩, ⟨decodeRow 12 ("51760342", 8), 1125⟩, ⟨decodeRow 12 ("17603452", 6), 1126⟩])
                  (.leaf [⟨decodeRow 12 ("21760354", 8), 1125⟩, ⟨decodeRow 12 ("17603524", 8), 1126⟩, ⟨decodeRow 12 ("76035214", 8), 1127⟩, ⟨decodeRow 12 ("60352174", 8), 1128⟩, ⟨decodeRow 12 ("03521764", 6), 1129⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("40352167", 6), 1128⟩, ⟨decodeRow 12 ("74035261", 8), 1127⟩, ⟨decodeRow 12 ("40352671", 8), 1128⟩, ⟨decodeRow 12 ("03526741", 8), 1129⟩])
                  (.leaf [⟨decodeRow 12 ("35267401", 8), 1130⟩, ⟨decodeRow 12 ("52674031", 8), 1131⟩, ⟨decodeRow 12 ("26740351", 6), 1132⟩, ⟨decodeRow 12 ("12674053", 8), 1131⟩, ⟨decodeRow 12 ("26740513", 8), 1132⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("67405123", 8), 1133⟩, ⟨decodeRow 12 ("74051263", 6), 1134⟩, ⟨decodeRow 12 ("37405162", 8), 1133⟩, ⟨decodeRow 12 ("74051632", 8), 1134⟩])
                  (.leaf [⟨decodeRow 12 ("40516372", 8), 1135⟩, ⟨decodeRow 12 ("05163742", 8), 1136⟩, ⟨decodeRow 12 ("51637402", 6), 1137⟩, ⟨decodeRow 12 ("25163704", 8), 1136⟩, ⟨decodeRow 12 ("51637024", 8), 1137⟩])))))
          (.branch 36
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("16370254", 8), 1138⟩, ⟨decodeRow 12 ("63702514", 6), 1139⟩, ⟨decodeRow 12 ("46370215", 8), 1138⟩, ⟨decodeRow 12 ("63702145", 8), 1139⟩])
                  (.leaf [⟨decodeRow 12 ("37021465", 8), 1140⟩, ⟨decodeRow 12 ("70214635", 6), 1141⟩, ⟨decodeRow 12 ("57021436", 8), 1140⟩, ⟨decodeRow 12 ("70214356", 8), 1141⟩, ⟨decodeRow 12 ("02143576", 8), 1142⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("21435706", 8), 1143⟩, ⟨decodeRow 12 ("14357026", 6), 1144⟩, ⟨decodeRow 12 ("61435720", 8), 1143⟩, ⟨decodeRow 12 ("14357260", 8), 1144⟩])
                  (.leaf [⟨decodeRow 12 ("43572610", 6), 1145⟩, ⟨decodeRow 12 ("04357216", 8), 1144⟩, ⟨decodeRow 12 ("43572106", 8), 1145⟩, ⟨decodeRow 12 ("35721046", 8), 1146⟩, ⟨decodeRow 12 ("57210436", 6), 1147⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("65721034", 8), 1146⟩, ⟨decodeRow 12 ("57210364", 8), 1147⟩, ⟨decodeRow 12 ("72103654", 8), 1148⟩, ⟨decodeRow 12 ("21036574", 8), 1149⟩])
                  (.leaf [⟨decodeRow 12 ("10365724", 6), 1150⟩, ⟨decodeRow 12 ("41036527", 6), 1149⟩, ⟨decodeRow 12 ("74103625", 8), 1148⟩, ⟨decodeRow 12 ("41036275", 8), 1149⟩, ⟨decodeRow 12 ("10362745", 8), 1150⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("03627415", 8), 1151⟩, ⟨decodeRow 12 ("36274105", 8), 1152⟩, ⟨decodeRow 12 ("62741035", 6), 1153⟩, ⟨decodeRow 12 ("56274130", 8), 1152⟩])
                  (.leaf [⟨decodeRow 12 ("62741350", 8), 1153⟩, ⟨decodeRow 12 ("27413560", 6), 1154⟩, ⟨decodeRow 12 ("02741365", 8), 1153⟩, ⟨decodeRow 12 ("27413605", 8), 1154⟩, ⟨decodeRow 12 ("74136025", 8), 1155⟩]))))
            (.branch 18
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("41360275", 8), 1156⟩, ⟨decodeRow 12 ("13602745", 8), 1157⟩, ⟨decodeRow 12 ("36027415", 6), 1158⟩, ⟨decodeRow 12 ("53602714", 8), 1157⟩])
                  (.leaf [⟨decodeRow 12 ("36027154", 8), 1158⟩, ⟨decodeRow 12 ("60271534", 6), 1159⟩, ⟨decodeRow 12 ("46027135", 8), 1158⟩, ⟨decodeRow 12 ("60271345", 8), 1159⟩, ⟨decodeRow 12 ("02713465", 8), 1160⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("27134605", 8), 1161⟩, ⟨decodeRow 12 ("71346025", 6), 1162⟩, ⟨decodeRow 12 ("57134620", 8), 1161⟩, ⟨decodeRow 12 ("71346250", 8), 1162⟩])
                  (.leaf [⟨decodeRow 12 ("13462570", 8), 1163⟩, ⟨decodeRow 12 ("34625710", 8), 1164⟩, ⟨decodeRow 12 ("46257130", 6), 1165⟩, ⟨decodeRow 12 ("04625731", 8), 1164⟩, ⟨decodeRow 12 ("46257301", 8), 1165⟩])))
              (.branch 9
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("62573041", 8), 1166⟩, ⟨decodeRow 12 ("25730461", 6), 1167⟩, ⟨decodeRow 12 ("12573064", 8), 1166⟩, ⟨decodeRow 12 ("25730614", 8), 1167⟩])
                  (.leaf [⟨decodeRow 12 ("57306124", 6), 1168⟩, ⟨decodeRow 12 ("45730621", 8), 1167⟩, ⟨decodeRow 12 ("57306241", 8), 1168⟩, ⟨decodeRow 12 ("73062451", 8), 1169⟩, ⟨decodeRow 12 ("30624571", 8), 1170⟩]))
                (.branch 4
                  (.leaf [⟨decodeRow 12 ("06245731", 8), 1171⟩, ⟨decodeRow 12 ("62457301", 6), 1172⟩, ⟨decodeRow 12 ("16245703", 8), 1171⟩, ⟨decodeRow 12 ("62457013", 8), 1172⟩])
                  (.leaf [⟨decodeRow 12 ("24570163", 8), 1173⟩, ⟨decodeRow 12 ("45701623", 6), 1174⟩, ⟨decodeRow 12 ("34570126", 8), 1173⟩, ⟨decodeRow 12 ("45701236", 8), 1174⟩, ⟨decodeRow 12 ("57012346", 8), 1175⟩])))))))))

theorem rows_eq : tree.flatten.map Point.row = Halfar0.rows := by rfl

theorem excesses_eq : tree.flatten.map Point.excess = Halfar0.prefixes := by rfl

noncomputable def point (i : Nat) : Option Point := tree.get? i

theorem point_sound (i : Nat) {p : Point} (hp : point i = some p) :
    p.Occurs Halfar0.rows :=
  PointTree.get_sound tree Halfar0.rows Halfar0.prefixes rows_eq excesses_eq
    Halfar0.prefixes_checked i hp

end SuperpermutationUpperBound.Native14.Pointers.FastHalfar0
