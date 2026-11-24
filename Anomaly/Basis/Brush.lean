import Anomaly.Basis.Fettle
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Py.Rate.BScale Mew PowerSeries
open scoped Mew
open Swell Porticus Tye Bake Neon Pressure
variable {n m N B:Side} {I:Type} [LinearOrder I] [Fintype I] {C:BudgetPoint} {h v u z w s:ℝ} {q k L':ℕ}
local notation "θ" => mid N B
local notation "δp" => C.supportExponent
local notation "BX" X:max => temple k C X
abbrev pozV (i:Seat n)(C:BudgetPoint)(k:ℕ)(J:Firing n): Bag n := fun X=> if X=temple k C i then J else 0
lemma chartCross (x:Seat n) (A:Firing n) (p:Herb C q (temple k C x) h A v):Barrage C q (grooveB k C x) h (pozV x C k A) s (v*tact s C.B (temple k C x)) (v*tact s C.B (temple k C x)):= Barrage.single _ _ (Flight.once p) le_rfl -- syntax `..`
abbrev momHub (k:ℕ)(C:BudgetPoint)(x:Seat n): Scree.Hub n:=⟨(x,grooveB k C x),halo_subset _ _ (mem_singleton_self x)⟩
lemma offset_P (x:Seat n)(A:Firing n):giveB (pozV x C k A)= A:=by unfold giveB pozV; simp
abbrev axleCap (k:ℕ):=3*Fief.tileN k
lemma pricedCap (k:ℕ)(x:Seat n) (P:BudgetPoint) :coverNumber P.B (temple k P x).val ≤ axleCap k:=by
 let G:=Dial.idrat (More n); have u:= P.B_pos; have w:(G.count).val=1:=rfl; have hp:= Fief.surgeK G {x} P.B k (.single x) u
 have hi:Finset.image G.parent {x}= {x}:=by rw [show G.parent=id from funext fun x=>by nth_rw 1 [← Dial.glass x]; exact Ratio.embed_parent .., image_id]
 rw [hi,card_singleton,w,Nat.one_mul] at hp
 refine Nat.le_of_mul_le_mul_left ?_ u -- tune
 refine hp.trans ((Nat.mul_le_mul_right (Fief.tileN k) (m:=P.B*3) ?_).trans_eq ?_)
 · exact (show 2*1+P.B≤ P.B*3 from by omega)
 unfold axleCap; rw [Nat.mul_assoc]
def cashPoncho (P s:ℝ)(k:ℕ):ℝ:= P* Real.exp (s*(axleCap k : ℝ))
lemma charm (x:Seat n)(A:Firing n)(p:Herb C q (temple k C x) h A v)(z:0≤ s):Barrage C q (grooveB k C x) h (pozV x C k A) s (cashPoncho v s k) (cashPoncho v s k):=by
 have hv:v*tact s C.B (temple k C x)≤ cashPoncho v s k:= mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (pricedCap k x C)) z)) p.price; exact (chartCross x A p).bigR hv hv -- implicit `_`
section Pole
variable (x:Seat n){J:Firing n} {G F:Aura n→ℝ}(U:∀ X, Flight C q X h ((pozV x C k J) X) (G X) (F X))(τ:Ids n)
local notation "Aq"=> pozV x C k J
local notation "Qv"=> singlePole τ Aq U x
local notation "K★"=> momHub k C x
include U
lemma loaded_R (Y:Scree.Hub n)(p:Y≠ momHub k C x): Qv Y=0:=by
 by_cases k':Y.val.1=x; swap; · exact station _ _ _ (fun (_:Fin 1) i=>U i) _ _ (0:Fin 1) Y k'
 funext V; apply Subtype.ext; rw [pole_value _ _ _ x k']; rw [show Aq (lagE Y)=0 from if_neg (fun (v:lagE Y= BX x)=> p (Subtype.ext (Prod.ext k' (congrArg Subtype.val v))))]; simp [coll_T,Sault.rind] -- tune syntax
lemma temple_Inc (T:PressB C K★ (Qv K★) h v)(h':1≤h):IncX primeU Qv C h (cashPoncho v C.supportExponent k):=by
 refine ⟨⟨Pi.single K★ v,?_ ,?_⟩,fun _ p=> p.elim⟩
 · intro i; by_cases e:i=K★; · subst i; rw [Pi.single_eq_same]; exact T
   rw [Pi.single_eq_of_ne e, loaded_R x U τ i e]; exact Vale.rinse ..
 intro i; rw [sum_eq_single K★]; swap; · intro j _ y; split; rw [Pi.single_eq_of_ne y]; exact mul_zero _; rfl
 swap; · simp
 have hv:0 ≤ v:=gradeE _ _ T (zero_le_one.trans h'); rw [Pi.single_eq_same]; split; swap; exact mul_nonneg hv (Real.exp_pos ..).le
 apply le_trans _ (b:= Real.exp (C.supportExponent*(axleCap k:ℝ))*v) (mul_comm ..).le; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (pricedCap k x C)) C.exponent_pos.le)) hv
lemma ink_same (T:PressB C K★ (Qv K★) h v) (I:InkD n) (P:∀ V:Pane n,pingS C.threshold (grooveB k C x) V → I V= Qv K★ V)
    (Q:PressB C K★ I h w) : PressB C K★ (Qv K★) h w:=by
 obtain ⟨a,h,p,w⟩:=Q.worth
 refine ⟨T.term,T.fitted,T.measureV,T.gaugeV,a,h,fun i v j=>?_ ,w⟩; refine Prism.mint (p i v j) (?_); change (fun y:tangD n=>_) =ᶠ[_] _; have ht:∀ᶠ y:tangD n in 𝓝 0,pingS C.threshold (grooveB k C x) (RG.increment i y):=by apply (show Continuous (RG.increment i) from (by unfold RG.increment; fun_prop)).continuousAt.eventually_mem (ping_o.mem_nhds ?_); change pingS _ _ _; rw [show RG.increment i 0=i from by funext j; simp [RG.increment]]; exact v
 filter_upwards [ht] with y hy; rw [P _ hy]
end Pole
variable {o:Site (mid N B)}{Z:Firing (mid N B)} (Kz:Herb C q (temple k C (node o)) h Z v) (h':1≤h) (hp:3 ≤ C.B) (δ:0 ≤ s)
local notation "Kν"=> momHub k C (node o)
local notation "Λz"=> pozV (node o) C k Z
lemma ratesSame {Q W: InkD (mid N B)}(x:∀ V:Pane (mid N B),pingS C.threshold (grooveB k C (node o)) V→ Q V=W V): pillar o Q C= pillar o W C:=by
 apply Prod.ext; funext i j; change iteratedFDeriv _ _ _ _ _ = _; have h:Taxi.lifeH Q ∘ RG.increment 1=ᶠ[𝓝 0] Taxi.lifeH W ∘ RG.increment 1:=by
    have h: Continuous (RG.increment (1:Pane θ)):=by unfold RG.increment; fun_prop
    apply ((h.tendsto 0).eventually ((show IsOpen {V:Pane θ|pingS C.threshold (grooveB k C (node o)) V} from ping_o).mem_nhds (by change pingS _ _ _; rw [show RG.increment 1 (0:tangD θ) = 1 from by funext i; simp [RG.increment]]; exact ping_f C _))).mono; intro t e -- wrong target: h comp with h at left => point equality; filter `.eventually`. tune
    change Pastry.pane _= _; rw [x _ e]; rfl
 rw [(h.iteratedFDeriv ℝ 2).eq_of_nhds]; rfl
 change Hove.jetsL _ (Haro.orbitPH (Q 1))=_; rw [x 1 (ping_f C _)]; rfl
include Kz hp h' δ
lemma gain_core {I: InkD (mid N B)} (H:PressB C Kν I h u) (L:∀ V:Orbit (mid N B), pingS C.threshold (grooveB k C (node o)) V.1→ Sault.rind (Z V)=(I V.1).val)
 (p: (axleCap k)^3<L'):
 Drill C q k L' o h s Λz (pillar o I C) (cashPoncho v s k) (cashPoncho u δp k) 0 := by
 refine ⟨charm _ _ Kz δ,?_⟩; intro G F t A; let U:=singlePole t Λz A (node o); have hz:Λz (BX (node o))=Z:=if_pos rfl
 have e:∀ V: Pane θ,pingS C.threshold (grooveB k C (node o)) V → U Kν V=I V:=by
    intro W p; apply Subtype.ext; unfold U; rw [rootVisible Kν A t _ rfl (V:=(W,t)) p, show lagE Kν=BX (node o) from rfl,hz]; exact L _ p
 have he:=heated _ _ _ (fun (_:Fin 1) i=> A i) t (node o) (0:Fin 1) hp (zero_le_one.trans h') Kν
 refine ⟨temple_Inc _ A t (ink_same _ A t he I (fun V p=>(e V p).symm) H) h', ?_,fun i p=> loaded_R _ A t i (fun y:i= Kν=>p (y ▸ rfl))⟩
 rw [show pilasters L' C o U= pillar o I C from ?_] -- target U defeq
 · simp
 unfold pilasters; rw [sum_eq_single Kν]; exact ratesSame e
 · intro X t v'; change pillar o (U X) C=_; rw [show U X=0 from loaded_R _ A _ X v', Pill_0 o C]
 intro h; exact (h (mem_filter.mpr ⟨mem_univ _,rfl, (Nat.pow_le_pow_left (pricedCap k (node o) C) _ |>.trans_lt p)⟩)).elim
lemma debitExtra (p:AuraOp C (BX (node o)) ∅ Z h z):
 let X:= (fareX C.B C (Kν).val.2*z); let W:=cashPoncho X C.supportExponent k; Drill C q k L' o h s Λz 0 (cashPoncho v s k) W (AxStamp.Ρpost C W):=by
 intro X W; refine ⟨charm _ _ Kz δ,?_⟩; intro G F t A; have hx:PressB C Kν (singlePole t Λz A (node o) Kν) h X:=by
    apply fringe_pole Kν A t _ rfl _ _ (zero_le_one.trans h'); rw [show Λz (lagE Kν)=Z from if_pos rfl]; exact Fringe.whole p
 apply AxStamp.simple (temple_Inc _ A t hx h') h'; exact fun i d=> loaded_R _ A _ i (fun v:i=Kν=>d (v ▸ rfl))
end YM.CF.Vow.TreasuryFog
