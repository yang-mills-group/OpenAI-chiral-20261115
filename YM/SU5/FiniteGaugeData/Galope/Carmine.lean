import YM.SU5.FiniteGaugeData.Galope.Tambour
import YM.SU5.FiniteGaugeData.Galope.Silent
/-! # Cash ledger in UNAveraged orientation, organizer controls which misses. Generic applicable to functions paying in this one bill. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Next.Rank Spindle Next.SectorChange
open Pressure Precision Laurent Bloch Exterior Next.Fluctuations
open Drachma Drachma.Toffee Avenue Wrist Press Poeme Haute Rally
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge} {s:Stage}{R:PathData G}{P:Bed}{M k w v:ℕ}{A:Finset (Cell n)}{Z:Finset (Site n)}{o:Site n}{γ C r x Λ α η τ μ a h:ℝ}
namespace Lantern
local notation "φ₀" => s.clip
variable {I:Finset (Bond n)}{β:ℝ}{J:ChartRatio G}
abbrev Others(I:Finset (Bond n)):=Subtype (fun i:Bond n=> i∉ I)
abbrev Batch(G:Gauge)(I:Finset (Bond n)):= LinkArray G (↥I)
abbrev Ocean(G:Gauge)(I:Finset (Bond n)):= LinkArray G (Others I)
def canal(G:Gauge)(I:Finset (Bond n)): Config G n ≃ᵐ Batch G I × Ocean G I:= MeasurableEquiv.piEquivPiSubtypeProd (fun _=>G.El) (fun x=>x∈I)
lemma part_meas (G:Gauge)(I:Finset (Bond n)): MeasurePreserving (canal G I) (prior G n) ((piHaar G (↥I)).prod (piHaar G (Others I))) := by unfold prior piHaar canal; convert! measurePreserving_piEquivPiSubtypeProd (fun _=>G.probHaar) (fun x:Bond n=>x∈I)
def makeup(O: Ocean G I)(X:Batch G I): Config G n:= (canal G I).symm (X,O)
abbrev Bleach(O:Ocean G I):= makeup O (1:Batch G I)
lemma it_others(O:Ocean G I)(X:Batch G I)(i:Bond n)(p:i∉ I): makeup O X i = O ⟨i,p⟩:= congr_fun (congr_arg Prod.snd ((canal G I).apply_symm_apply (X,O))) (⟨i,p⟩: Others I)
lemma it_batch(O:Ocean G I)(X:Batch G I)(i:Bond n)(p:i∈I): makeup O X i=X ⟨i,p⟩:= congr_fun (congr_arg Prod.fst ((canal G I).apply_symm_apply (X,O))) (⟨i,p⟩:↥I)
lemma makeup_ok(O:Ocean G I): Measurable (makeup O):= (canal G I).symm.measurable.comp (measurable_id.prodMk measurable_const)
-- horizontal link coordinates in the little gauges (vs actual prior)
def onRoad(s₁:Site n→G.El)(X:Batch G I): Batch G I:=fun y=> (s₁ y.val.1)⁻¹ * X y * (s₁ (y.val.1+step y.val.2))
lemma onRoad_mp(s₁:Site n→G.El): MeasurePreserving (onRoad (I:=I) s₁) (piHaar G (↥I)) (piHaar G (↥I)) := measurePreserving_pi (μ:=fun _=>G.probHaar) (ν:=fun _=>G.probHaar) (fun (x:↥I)=> G.preserve_two_sided (s₁ x.val.1)⁻¹ (s₁ (x.val.1+step x.val.2)))
lemma kits_batch(O:Ocean G I)(X:Batch G I)(s₁:Site n→G.El)(i:↥I): gauge s₁ (makeup O (onRoad s₁ X)) i.val=X i:=by unfold Lattice.gauge; rw [it_batch _ _ _ i.2]; unfold onRoad; dsimp only [Subtype.coe_eta]; group -- tune

section funding
variable (F: Config G n→ℝ)(e:ℝ)
lemma int_e (p: Envelope F) {K:Type}[MeasurableSpace K] (ν:K→ Config G n) (h:Measurable ν): Envelope (F∘ν):=⟨p.meas.comp h, let ⟨q,t⟩:=p.cost; ⟨q,fun v=> t (ν v)⟩⟩ -- universe tune
lemma silo (p:Envelope F)(hp:∀ O:Ocean G I,(∫ x,F (makeup O x) ∂piHaar G (↥I))≤e): (∫ x,F x∂prior G n) ≤ e:=by
 let c:=part_meas G I; let f:=F ∘ (canal G I).symm
 have he:(∫ x,F x∂prior G n)=(∫ x, f x∂(piHaar G (↥I)).prod (piHaar G (Others I))):= (c.symm.integral_comp' F).symm
 rw [he]; let J':= c.symm.integrable_comp_of_integrable (p.integrable _); rw [integral_prod_symm f J']; exact (integral_mono (J'.integral_prod_right) (integrable_const e) hp).trans_eq (by simp)
end funding

-- event support.L. Tangent assets on all tiles.
variable (O: Ocean G (buy Z k)) (F:Arms G s)
variable {V: Batch G (buy Z k)}
abbrev orient(O:Ocean G I)(Z:Finset (Site n))(M:ℕ):= mapA (Bleach O) Z M
def Vogue(Z:Finset (Site n))(M k:ℕ)(O:Ocean G (buy Z k))(V:Batch G (buy Z k)): Config G n:= makeup O (onRoad (orient O Z M) V)
abbrev care(O: Ocean G (buy Z k))(M:ℕ)(V:Batch G (buy Z k)): Config G n:=gauge (orient O Z M) (Vogue Z M k O V)
-- for fixed O, off-batch values of $costs$ are constants. pack from a reference independent of V.
lemma stall(O:Ocean G (buy Z k))(V:Batch G (buy Z k))(i:Bond n)(p:i∉ buy Z k): care O M V i=care O M (1:Batch G _) i:=by unfold care Lattice.gauge Vogue; rw [it_others _ _ _ p,it_others _ _ _ p]
def flake(O: Ocean G (buy Z k))(M:ℕ): LogField G n:= LiftKit (fun i=>if i∈ buy Z k then 0 else shipX (care O M (1:Batch G (buy Z k))) Z M i)

lemma section_bound (hv:0≤x)(hz:Z⊆glow A M)(hm:k<M)(hs:2*(M+1)<n.val)(V:Batch G (buy Z k)) (z:∀ i: Cell n,i∈A↔ x<G.chord (faceValue (Vogue Z M k O V) i)) (hx:balanceX M x ≤ F.allowance.c):
 let Y:=care O M V; let g:=assetX Y Z M; let b:= 2*balanceX M x
 ∃ X:LogArray G (↥(buy Z k)), (∀ i,‖X i‖≤ b)∧ release 1 X=V ∧ ‖g‖ ≤ b ∧ (∀ i∈ RoomsM M Z, Y i=represent g i) ∧ g= flake O M + kickC (buy Z k) (tape.symm X) :=by
 intro Y g b; let Val:= Vogue Z M k O V; let ν:=orient O Z M; let X(i:↥(buy Z k)):= g (tabKey _ i)
 have hv1(x:Bond n)(p:x∉ buy Z k): Val x= Bleach O x:=by unfold Val Vogue Bleach; rw [it_others _ _ _ p,it_others _ _ _ p]
 have hv2(i:Bond n)(p:i∈ RoomsM M Z): G.chord (Y i)≤balanceX M x:=by
    obtain ⟨j,t,h⟩:= mem_biUnion.mp p; exact cargoF Val (Bleach O) hz t hs hm.le hv1 _ hv (fun i g=>le_of_not_gt ((z i).not.mp g)) i h
 obtain ⟨h,hX⟩:=boundedX F Y (show 0≤balanceX M x by unfold balanceX; positivity) hx hv2
 refine ⟨X,fun i=>(norm_le_pi_norm g (tabKey _ _)).trans h,?_,h,hX,?_⟩
 · funext i; unfold release; rw [Pi.one_apply,mul_one, ←kits_batch O V ν i]; change _=Y i; rw [hX _ (buying hm i.2)]; change _=G.lieExp _ * 1; rw [mul_one]; rfl
 funext y; obtain ⟨x,rfl⟩:= (portfolio n).surjective y; simp only [Pi.add_apply]; by_cases p:x∈buy Z k
 · let i:↥(buy Z k):=⟨x,p⟩; have ht:flake O M (portfolio _ x)=0:=(liftKit_on ..).trans (if_pos p); rw [ht,zero_add]; exact ((at_tab (tape.symm X) i).trans (show _=X i from rfl)).symm -- tune
 unfold flake; unfold g Y assetX; rw [show portfolio n x=markZ n x from rfl,liftKit_on,liftKit_on, at_key _ _ p,add_zero,if_neg p,shipX,shipX,stall _ _ x p]

namespace Cup
-- exp cost decomposition aggregated all links.W.
abbrev heightK(p:BudgetPoint)(M:ℕ):= 2*balanceX M p.threshold
abbrev gross(w:ℕ)(s:Stage)(β α:ℝ):= (1-primeShare w s)*((1-α)*β)
abbrev greatF(F:Arms G s)(n:Side)(w M:ℕ)(p:BudgetPoint)(β α Λ:ℝ):= β*((Fintype.card (Cell n):ℝ)*((priceP F w (heightK p M))^2/α))+CF.Graph.taxY n β p.threshold s.paths Λ
abbrev bonusK(p:BudgetPoint)(s:Stage)(β:ℝ):= β*(s.clip.linear*p.threshold^2)
abbrev feeZ (F:Arms G s)(J:ChartRatio G)(p:BudgetPoint)(β α Λ μ:ℝ)(P:Bed)(A: Finset (Cell n))(Z:Finset (Site n))(k w M:ℕ) :ℝ := (J.scale*μ)^(buy Z k).card*Real.exp (greatF F n w M p β α Λ - A.card*bonusK p s β)*holdK (chrome G P Z k) (gross w s β α)
open Set
-- Avoid costly nested goal on PP.S
structure Attains (F:Arms G s)(J:ChartRatio G)(n:Side)(p:BudgetPoint)(β α μ:ℝ)(M k w:ℕ) :Prop where
 warm : 0<β
 witness : 0<α
 legal : α<1
 spry : 0<gross w s β α
 tall : debit k w ≤ M
 wide : 2*(M+1)<n.val
 homeF : 0<μ
 lucent : Lucent J (heightK p M) μ
 rood : heightK p M ≤ F.r
 frameH : balanceX M p.threshold ≤ F.allowance.c
 atfar : 2≤p.threshold*Real.exp ((w:ℝ)/s.clip.relaxation)
variable {p:BudgetPoint} {F}
lemma only_pays (P:Bed)(T: Attains F J n p β α μ M k w)(hz:Z⊆ glow A M) (Q:Floor P φ₀ n a C)(u:0<a)(W:R.Bounds φ₀ s.width s.paths Λ)(hW:Attached P R)
 (U: Config G n→ℝ)(q:Envelope U)(h0:∀ V:Config G n,U V≠0→ (∀ i:Cell n,i∈A↔ p.threshold<G.chord (faceValue V i)) ∧ U V≤ Real.exp (- R.principal φ₀ p β V)) :
 (∫ i,U (makeup O i) ∂ piHaar G (↥(buy Z k))) ≤ feeZ F J p β α Λ μ P A Z k w M:=by
 let I:= buy Z k; let S:= piHaar G (↥(buy Z k)); let ν:= orient O Z M; let U' (i:Batch G (buy Z k)):= U (Vogue Z M k O i); let T':= chrome G P Z k; let r:= gross w s β α; have hh: r>0:= T.spry; let t:= greatF F n w M p β α Λ; let codA:= bonusK p s β; let E:= Real.exp (t-A.card*codA)
 have hz' := onRoad_mp (I:=buy Z k) ν; have hm:k<M:=by refine Nat.lt_of_lt_of_le ?_ T.tall; unfold debit roomCard; omega
 have hy: (∫ i,U (makeup O i) ∂S) =(∫ i,U' i∂S):=by
    let V(i):=U (makeup O i); have hv:=integral_map (μ:=S) (f:=V) hz'.measurable.aemeasurable (by rw [show S=_ from rfl,hz'.map_eq]; exact (q.meas.comp (makeup_ok O)).aestronglyMeasurable); rw [hz'.map_eq] at hv; exact hv -- tune
 rw [hy]; let origin:=flake O M; obtain ⟨m,v⟩:= offer (Z:=Z) hm.le (hz.trans (glow_in ..)) origin Q W hW w
 have hκ:0<β:= T.warm; have hw:0<(1-α)*β/2:=by have hp:=sub_pos.mpr T.legal; positivity
 unfold feeZ; rw [←Fintype.card_coe]
 refine Rally.price T.lucent T.homeF.le U' (int_e U q _ (show Measurable (Vogue Z M k O) from (makeup_ok O).comp hz'.measurable)) T' (live_sigma G Q u) hh (Real.exp_pos _).le m ?_ -- int_e comp fill implicit
 intro j b; let V:=Vogue Z M k O j; let Y:=care O M j; obtain ⟨p',he'⟩:=h0 V b; obtain ⟨x,c,g,l,br,f⟩:= section_bound O F p.threshold_pos.le hz hm T.wide j p' T.frameH; let f':= x; refine ⟨x,g,c,?_⟩
 let d:= tape.symm x; let K:=assetX Y Z M; let K₀:=origin + kickC I d; have hf: K=K₀:= f
 have he:= weights (k:=k) F p V Y ν rfl K W br hz p' T.atfar T.tall l T.rood hκ.le T.witness T.legal.le
 let D(w:Prices G (↥(buy Z k))): ℝ:= dotProduct w (T'*ᵥ w) -- replace
 change U V≤ E*doll T' (d+m) r; apply he'.trans; unfold E doll; rw [← Real.exp_add]; refine Real.exp_monotone ?_
 change (1-α)*β/2*accepts s R (billsC k w Z) K+β* (A.card * (s.clip.linear *p.threshold^2)) ≤ _ at he
 rw [hf] at he; change -_≤ t-_+ -r/2 * D (d+m); unfold t r codA greatF gross bonusK D; linarith only [he, mul_le_mul_of_nonneg_left (v d) hw.le]
end Cup
end Lantern
end YM.SU5.FiniteGaugeData.Galope
