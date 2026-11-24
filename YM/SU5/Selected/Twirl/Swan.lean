import YM.SU5.Selected.Cor.Amber
import YM.SU5.Selected.Twirl.Pearl
import YM.SU5.Selected.Twirl.Tome
/-!
# One adjacent-price estimate on SAME election (all small δ and comparison horizon)
Assembly to hand to χ-spectrum consumers. Stay with this History. Shift-probed $rank 오$.
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open YM.CF.Pannier.Chancel.Lantern
variable (H:Real.exp 1≤ P.x)
open Crest
namespace Mileage
local notation "κI" i:max s:max k:max => (gram Y s i k).J.M
local notation "SN" i:max s:max => Papal.count Y s i
open Bulb Bulb.Mezz
open Airy (Coast Wq)
open CF.Pannier.Chancel.Lantern (Station)
open CF.Pannier.Chancel.Lantern.Tender
open Afterglow.Tapestry
open Bulb.Commission
local notation "K"=> tent Y H
variable {A:Mezz}{C Ω:ℝ}{w:ℕ}{X Z:Coast→ Wq A.marks} {R:ℝ}
local notation "τ₀"=> billR C
variable {d:Type}[Fintype d][DecidableEq d](U:Society d)(s i k:ℕ)
variable {b g:ℕ}{ε E₀:ℝ}(t:Delay Y H b g ε Ω C E₀ A w X Z)
variable {i' k':ℕ→ℕ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}
   (V: Universal Y H i' k' I E)
local notation "W'"=> U.qu.kin
local notation "μ"=> 2*Real.exp (1-Ω)
local notation "β"=> A.Broad
local notation "η"=> t.stationed Y H
open Tapestry
local notation "Λ" F:max=> (Mezz.Sermon.solitude A K (η) F).val
local notation "α₀" F:max=> (Journey.sharp Y H s i k F)
local notation "Kc"=> momentm Y i s
local notation "K₀"=> (SN i s)
local notation "J" => CF.Pannier.Chancel.Lantern.Station.tollK (dueW τ₀)
local notation "vS" => ((CF.Pannier.Chancel.Lantern.Station.tollK (dueW τ₀)) ^ A.vowP)
namespace Delay
variable (c:A.Caste (N:=Papal.count Y s i) (gram Y s i k).J.M C (tightH A.D (billR C)) w X Z)(hp: Luster Y U s i k Ω C A w X Z c)
local notation "α₁" F:max => (Tower.mirror (K) 3 0 F*F) -- use K const outside variable

include c hp
lemma price_BF (F:Buffered.Family (tent Y H))(hF: arrange _ (SN i s) (terrain Y H (Y.ir i) s) (F (Kc)) = (A.triumph U X Z C c).frame): ‖Journey.sharp Y H s i k (α₁ F)‖ ≤ (μ) ∧ ∀ x, ‖(α₁ F) (Kc) x‖ ≤ (vS)^ (2:ℕ):=by
 let M:= A.triumph U X Z C c; let x:=F; let Θ:= (SN i s); let Z':= α₁ x; let P':= exhibit Y H s i; have hu:P' Z'= reflMark 3 0 M.frame *M.frame:= by unfold P' Z'; rw [actual_product,Tower.mirror_time, actual_reflect, show exhibit Y H s i _= _ from (show exhibit Y H s i x=M.frame from hF)] -- rw tune
 refine ⟨(by change ‖Journey.sharp Y H s i k Z'‖ ≤ _; rw [actualRead, (show exhibit Y H s i Z'= _ from (hu : P' Z'= _))]; exact hp.price),?_⟩
 apply (displayPositive (terrain Y H (Y.ir i) s) ((vS)^(2:ℕ)) ((α₁ x) (Kc))).mpr; intro i; change ‖P' Z' i‖ ≤ _; rw [hu]; -- may need fold Z'
 change ‖reflMark 3 0 M.frame i * M.frame i‖ ≤ _; apply le_trans (norm_mul_le ..); rw [show ‖reflMark 3 0 M.frame i‖=_ from (Afterglow.theta_fee ..), sq]; exact mul_le_mul (hp.quote _) (hp.quote _) (norm_nonneg _) ((norm_nonneg _).trans (hp.quote i)) -- param `eq P'.`

omit c hp
end Delay
open Tower.SlabMark
-- both prices. t same, d' Var parameters all shared. Spend uppercase P history. include rides.
local notation "μμ"=> rapids P.block A.marks
local notation "A'"=> A.pumped (rapids P.block A.marks)
local notation "Yd"=> stint P.block A.marks
-- No notation using section-var inside variable decls!! prevents silent sorrys.
structure Effigy (Ω:ℝ)(b g:ℕ)(ε:ℝ)(C E₀:ℝ)(A:Mezz)(w:ℕ)(X X₁ Z:Coast→ Wq A.marks): Prop where
 first_: Delay Y H b g ε Ω C E₀ A w X Z
 second_: Delay Y H b g ε Ω C E₀ (A.pumped (rapids P.block A.marks)) w X₁ Z
 lift : Crest.Airy.Lift A.marks (rapids P.block A.marks) X X₁
 start: A.ride=0
-- delivery from Tome: adapt pretension
lemma created (D:ℝ)(S':Supplier)(p0:0<Ω)(w' : decorate (radiantW Ω S') P l D ≤ P.h)(d': P.d ≤ austere)(h: Inflation D P) : decorate S' P l D≤ P.h ∧ ∃ (b g:ℕ)(ε C E₀:ℝ)(A:Mezz)(w:ℕ)(X X₁ Z:Coast→ Wq A.marks), Effigy Y H Ω b g ε C E₀ A w X X₁ Z:= by
 obtain ⟨hz,G,b,u,w,X,X',Z,R,C,E₁,v,γ,t',g,f⟩:= sunlit Y H Ω p0 S' w' d' h
 have hx:R=10000*C^ (4:ℕ):= t'.warmth; subst R
 let A:Mezz:= ⟨ G, fundD P.R.L b,⟨ u,t'.count⟩,⟨ addgap (tent Y H),addgap_pos⟩,⟨w+v+1,by omega⟩,0⟩
 have hp:w+v+1≤ A.W:=A.geo_q
 have h0:w ≤A.W:= by omega
 have h1:v ≤ A.W:=by omega
 refine ⟨hz,b,v,γ,C,E₁,A,w,X,X',Z,⟨rfl,t'.older,rfl,h0,h1,t'⟩,⟨rfl,t'.older,rfl,h0,h1,g⟩,f,rfl⟩

local notation "α₁" F:max => (Tower.mirror (K) 3 0 F*F) -- reused
variable {X':Coast→ Wq A.marks}(r:Effigy Y H Ω b g ε C E₀ A w X X' Z)
local notation "r₀"=> r.first_
local notation "r₁"=> r.second_
namespace Effigy
include H r
lemma reach : μμ ≤ A.passW:=by
 have hp: addgap (tent Y H) ≤ A.ℓ.val:= r.first_.slope.ge
 have hf: 8*P.block.val ≤ A.ℓ.val:=by refine le_trans ?_ hp; unfold addgap stepgap; change 8*P.block.val≤ 2*(_+4*P.block.val); omega
 have hc:=(Tender.swift P.block A.marks).2; unfold passW Mezz.n Tender.nudge Airy.harbor; omega
-- danger `r` include
omit H r
private lemma st_b{T:Mezz}{K':Calibration}{G:Society d}(X X₁ Z:Coast→ Wq T.marks)(C:ℝ)(n:ℕ)(m N:Side)(b:N=K'.c m){M:Tulip.Male}
    (c:T.Caste (N:=N) M C (tightH T.D (billR C)) w X Z)(c':(T.pumped n).Caste (N:=N) M C (tightH T.D (billR C)) w X₁ Z)(I:Crest.Airy.Lift T.marks n X X₁)(hv:n ≤ T.passW)(u: T.ride=0) (a:n=rapids K'.B T.marks)
    (p:∀ b (i:T.Lot),Roomy (T.yard i.1 b) N)(h:∀ i:T.BlockDay,Roomy (plow K' 3 (↑(stint K'.B T.marks)) (T.yard i true) ∪ T.yard i true) N): ∃ F F': Sermon T K' G.qu.kin, arrange _ N b.symm ((F.solitude T K' c.value).val m)=(T.triumph G X Z C c).frame ∧ arrange _ N b.symm ((F'.solitude T K' c.value).val m)= ((T.pumped n).triumph G X₁ Z C c').frame ∧ Mezz.Duet K' T (stint K'.B T.marks) F F':=by subst N; exact sidings K' T n G X X₁ Z C c c' I u hv a p h
variable (c':(A.pumped (rapids P.block A.marks)).Caste (N:=Papal.count Y s i) (gram Y s i k).J.M C (tightH A.D (billR C)) w X' Z)
local notation "N₀"=> K.c Kc
include H r
lemma for_horizon (e:∀ b (j:A.Lot),Roomy (A.yard j.1 b) (SN i s))(e':∀ i':A.BlockDay,Roomy (plow K 3 (↑(stint P.block A.marks)) (A.yard i' true) ∪ A.yard i' true) (SN i s))
    (c:A.Caste (N:=Papal.count Y s i) (gram Y s i k).J.M C (tightH A.D (billR C)) w X Z)(c':(A.pumped (rapids P.block A.marks)).Caste (N:=Papal.count Y s i) (gram Y s i k).J.M C (tightH A.D (billR C)) w X' Z)(p₁:Luster Y U s i k Ω C A w X Z c)(p₂:Luster Y U s i k Ω C (A.pumped (rapids P.block A.marks)) w X' Z c') :
    ∃ F F': Sermon A K W', Mezz.Duet K A (stint P.block A.marks) F F' ∧
     let u:= F.solitude A K c.value; let u':= F'.solitude A K c.value
     (‖Journey.sharp Y H s i k (α₁ u.val)‖ ≤ (μ) ∧ ∀ x, ‖(α₁ u.val) (Kc) x‖ ≤ (vS)^ (2:ℕ)) ∧
     (‖Journey.sharp Y H s i k (α₁ u'.val)‖ ≤ (μ) ∧ ∀ x, ‖(α₁ u'.val) (Kc) x‖ ≤ (vS)^ (2:ℕ)) :=by
 obtain ⟨F,F',pF,pF',he⟩:= st_b (T:=A) (K':=tent Y H) (G:=U) X X' Z C (μμ) (Kc) (SN i s) (terrain Y H (Y.ir i) s).symm c c' r.lift (reach Y H r) r.start rfl e e'
 exact ⟨F,F', he,(Delay.price_BF Y H U s i k c p₁ _ pF), Delay.price_BF (A:=A') Y H U s i k c' p₂ _ pF'⟩

include V U
local notation "ε₀"=> r.first_.stationed Y H
local notation "Λ₁" F:max=> (Mezz.Sermon.solitude A K (r.first_.stationed Y H) F).val
lemma attends : ∀ᶠ s in atTop,∃ (F F':Sermon A K U.qu.kin), ‖E s (α₁ (Λ₁ F))‖ ≤ 3*Real.exp (1-Ω) ∧ ‖E s (α₁ (Λ₁ F'))‖ ≤ 3*Real.exp (1-Ω) ∧ Mezz.Duet K A (Yd) F F' := by
 have ht:Real.exp (1-Ω) >0:= Real.exp_pos _; let ν:= Real.exp (1-Ω); let v:= (vS)^ (2:ℕ); have he: 1≤v:= one_le_pow₀ (one_le_pow₀ (Tender.toll_pos (by have hp:= r.first_.seed.price; change 0≤10000*C^ (4:ℕ); positivity))); filter_upwards [r.first_.whips Y H U,r.second_.whips Y H U] with s x w
 have hx : ∀ᶠ i in atTop, (∀ b (j:A.Lot),Roomy (A.yard j.1 b) (SN i s))∧ ∀ j:A.BlockDay,Roomy (plow K 3 (↑(stint P.block A.marks)) (A.yard j true) ∪ A.yard j true) (SN i s) := (eventually_all.mpr fun b=>eventually_all.mpr fun j=>roomyTail Y H s _).and (eventually_all.mpr fun j=>roomyTail Y H s _) -- conjunction
 let L:= V.pick.grow_i.tendsto_atTop; obtain ⟨i,⟨⟨hs,hw⟩,e⟩,t⟩:= ((((L.eventually x).and (L.eventually w)).and (L.eventually hx)).and (Council.total_precision Y H s V (β ∪ Tower.reflectedBox 3 0 β) ν v ht (by linarith))).exists
 obtain ⟨k,⟨⟨c,h⟩,c',h'⟩,f⟩:= ((V.pick.grow_k.tendsto_atTop.eventually (hs.and hw)).and (cadence Y k' V.pick.grow_k (i' i))).exists
 obtain ⟨F,F',p,x,x'⟩:= for_horizon Y H U s (i' i) (k' k) r e.1 e.2 c c' h h'
 let σ:= Journey.sharp Y H s (i' i) (k' k); have hz(F:Sermon A K W')(h:‖σ (α₁ (Λ₁ F))‖ ≤ (μ))(l:∀ x, ‖(α₁ (Λ₁ F)) (momentm Y (i' i) s) x‖ ≤ v): ‖E s (α₁ (Λ₁ F))‖ ≤ 3*Real.exp (1-Ω):=by
    let Y₀:= α₁ (Λ₁ F)
    have hc:= t k f _ (Delay.reflective (K) β (Λ₁ F) (blush (F.solitude A K (ε₀))).widen) l; have hc : ‖σ Y₀-E s Y₀‖≤ν:= hc; unfold ν at hc; change ‖σ Y₀‖ ≤_ at h
    change ‖E s Y₀‖ ≤ _; refine (norm_le_norm_sub_add _ (σ Y₀)).trans ?_; rw [norm_sub_rev]; linarith only [h,hc]
 exact ⟨F,F',hz F x.1 x.2,hz F' x'.1 x'.2,p⟩
omit U
lemma paired_choice : ∀ᶠ s in atTop,∀ W: Window.Family, ∃ (F F':Sermon A K W), ‖E s (α₁ (Λ₁ F))‖ ≤ 3*Real.exp (1-Ω) ∧ ‖E s (α₁ (Λ₁ F'))‖ ≤ 3*Real.exp (1-Ω) ∧ Mezz.Duet K A (Yd) F F' := by
 apply eventually_all.mpr; intro W; obtain ⟨T,u,w,Q,rfl⟩:= Society.families W; letI:= u; letI:= w; exact attends Y H Q V r
end Effigy
end Mileage
end Papal
end LocalLimit
end Rate
end YM.CF.Py
open YM.CF.Py.Rate.LocalLimit.Papal.Mileage
#print axioms Effigy.for_horizon
#print axioms Delay.price_BF
#print axioms created
#check @Effigy.paired_choice
#print axioms Effigy.reach
#print axioms Effigy.attends
#print axioms Effigy.paired_choice
