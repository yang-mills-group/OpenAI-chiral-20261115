import GaugeFieldConstruction.ChartreuseRP
/-!
 # arbitrary variable-state products, cap arrivals and continuity
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable {B:Small S C}{p q:ℝ≥0}{F:Waves S}{K:Spins S}{W:Surface S}{J:StarOp S}{D:∀ i,Blanket i}{R:S.Rotation}{s:S.RealSpin}
variable (d:PredictionL W F K J B R s){X:W.Aurora D}(H:X.FullBody F)(b: Hull B F J)
lemma nKernelRP (v:Fin n→Letter S)(w:Fin m→Letter S): W.W _ (bothT (Prod.fst ∘ v) (Prod.fst ∘ w) J) (bothTest v w J)= W.kernel J (List.ofFn v) (List.ofFn w) :=by
 rw [Surface.kernel]
 have he: List.ofFn (bothL v w J)=Sentence.rev J (List.ofFn v)++List.ofFn w:=by
    unfold bothL Sentence.rev; rw [List.map_ofFn, List.ofFn_fin_append,reverse_ofFn]; rfl
 rw [← he,expect_ofFn] -- tune
 unfold bothTest; congr 2
 funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [bothT,bothL,Letter.op]
variable (v:Fin n→ Letter S)(w:Fin m→ Letter S)
def forwardRP (x:Points n): Fin n→Letter S:=fun i=>((v i).1,Probe.ahead (x i) (v i).2)
lemma forward_stillRP: forwardRP v 0=v:=by ext i; all_goals simp [forwardRP]
lemma BothAheadRP (u:Points n)(z:Points m): bothTest (forwardRP v u) (forwardRP w z) J=Probe.ahead (bothP u z) (bothTest v w J):=by
 ext1 i; obtain ⟨⟨x,y⟩,rfl⟩:=merger.surjective i; change bothTest _ _ _ (bothP x y)= _
 rw [Probe.ahead_at]; change _= bothTest v w J ((bothP x y)-bothP u z)
 have hg: bothP x y-bothP u z=bothP (x-u) (y-z):=(merger.map_sub (x,y) (u,z)).symm
 rw [hg,bothTest_at,bothTest_at]; simp [forwardRP]
lemma BothMoveRP :Continuous (fun x:Points n × Points m=>bothP x.1 x.2):=merger.continuous
lemma aheadMoveRP (f:Joint n):Continuous (fun x:Points n=> Probe.ahead x f):=by
 have h:= Work.C08.continuous_affine_probe (fun z:Points n=> z) (fun _=> ContinuousLinearEquiv.refl ℝ (Points n)) f continuous_id continuous_const continuous_const
 refine h.congr fun x=>?_ ; ext; simp
lemma bothTestMoveRP:Continuous (fun x: Points n × Points m=> bothTest (forwardRP v x.1) (forwardRP w x.2) J):=by simp_rw [BothAheadRP]; exact (aheadMoveRP _).comp BothMoveRP
lemma BothHairRP:Continuous (fun x:Heights n × Heights m=> dawn (bothH x.1 x.2)):=by
 have hx:Continuous (dawn (n:=n+m)):=by unfold dawn place points; simp_rw [← Mink.combine_at]; fun_prop
 have hh:Continuous (fun x:Heights n × Heights m=> bothH x.1 x.2):=by
    apply continuous_pi; intro i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [bothH] <;> fun_prop
 exact hx.comp hh
variable {U:Type*}{l:Filter U}(y:U→ Heights n)(z:U→ Heights m)(p q:U→ℝ≥0)
lemma HairTendsRP (ha:Tendsto y l (𝓝 0))(hb:Tendsto z l (𝓝 0))(he:∀ᶠ i in l,Small.ample (p i) (y i))(hf:∀ᶠ i in l,Small.ample (q i) (z i)): Tendsto (fun i=>dawn (bothH (y i) (z i))) l (𝓝[shores (n+m)] 0):= by
    refine tendsto_nhdsWithin_iff.2 ⟨?_,?_⟩
    · have hz:Tendsto (fun i=>dawn (bothH (y i) (z i))) l (𝓝 (dawn (bothH (0:Heights n) (0:Heights m)))):= BothHairRP.continuousAt.tendsto.comp (ha.prodMk_nhds hb)
      have hp:dawn (bothH (0:Heights n) (0:Heights m))=0:=by
         ext1 i; refine Fin.addCases ?_ ?_ i <;> intro i <;> simp [dawn,bothH,place,← Mink.combine_at]
      rwa [hp] at hz
    filter_upwards [he,hf] with i ai bi using warmer _ (etched (ordered (roomPositive (ample_room ai)) (roomPositive (ample_room bi))))
include d H b
lemma shineRP (ha:Tendsto y l (𝓝 0))(hb:Tendsto z l (𝓝 0))(he:∀ᶠ i in l,Small.ample (p i) (y i))(hf:∀ᶠ i in l,Small.ample (q i) (z i))
    (u:U→ Points n)(r:U→ Points m)(t₀:Points n)(s₀:Points m)(hp:Tendsto u l (𝓝 t₀))(hq:Tendsto r l (𝓝 s₀)):
    Tendsto (fun i=> inner ℂ (capRP B (forwardRP v (u i)) (p i) (y i)) (capRP B (forwardRP w (r i)) (q i) (z i))) l (𝓝 (W.kernel J (List.ofFn (forwardRP v t₀)) (List.ofFn (forwardRP w s₀)))):=by
 let X':= W.W _ (bothT (Prod.fst ∘ v) (Prod.fst ∘ w) J); let L(i:U):=bothTest (forwardRP v (u i)) (forwardRP w (r i)) J; let M:=bothTest (forwardRP v t₀) (forwardRP w s₀) J; let f(i:U):= dawn (bothH (y i) (z i)); have hh:Tendsto f l (𝓝[shores (n+m)] 0) := HairTendsRP y z p q ha hb he hf
 have hu: Tendsto L l (𝓝 M):= by
    have hi:= ((bothTestMoveRP (J:=J) v w).tendsto (t₀,s₀)).comp (hp.prodMk_nhds hq)
    exact hi
 have hg:= partialJΛL (D _) L f _ M X' (flat _) hu hh
 have hr:= (D (n+m)).flatD (glazeL D _) (d.inlet.habitat (n+m) (bothT (Prod.fst ∘ v) (Prod.fst ∘ w) J)); change (D _).partialD X' 0= X' at hr; rw [hr] at hg
 rw[← nKernelRP]; change Tendsto _ _ (𝓝 (X' M)); refine hg.congr' ?_; filter_upwards [he,hf] with i ai bi
 exact (posKernelRP B (forwardRP v _) (forwardRP w _) d.inlet H b ai bi).symm
#print axioms shineRP
end YM.NSF.Boundary
end
