import YM.SU5.SatinWard.Resolution.Nimbus
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 85000
noncomputable section
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A:ℝ)
open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
open Hove Yoke Buffered Afterglow Journey ShapeLab.ResolutionFrame
namespace Tabletop

open ResolutionFrame Vow.TreasuryFog Swell
open ResolutionFrame Rue Advance Tapestry
variable {I:Type}[Fintype I][LinearOrder I]{v z:ℕ}
attribute [-instance] instDecidableEqLex
local notation "WK"=> Booth I η
local notation "Λs"=> P.Ctor (Y.ir i) (s+1)
local notation "Λv"=> P.Ctor (Y.ir i) v
local notation "E0"=> (Y.voyage i).CapeT
local notation "αs"=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "Ru"=> grantRadius P ℓ z
variable (σ:I→Site (P.Ctor (Y.ir i) s))
local notation "σ0"=> chassis η σ
local notation "σ1"=> chassis η (heel αs ∘ σ)
-- helpers
lemma bottom_host (i:WK)(l:List WK): distinctHost (i::l) ↔ (∀ j∈l,desk i ≠ desk j) ∧ distinctHost l:= by
 rw [distinctHost,List.map_cons,List.nodup_cons]; simp only [List.mem_map,not_exists,not_and,distinctHost,ne_eq,eq_comm (b:=desk i)]
lemma subhost (C:Finset WK)(v:List WK)(p:distinctHost v): distinctHost (Leit C v):= p.sublist (List.Sublist.map _ List.filter_sublist)
variable (V₀ : Booth I η→ Mark (P.Ctor (Y.ir i) s))(hx:∀ i,AtSupport false (offsetMask z ((chassis η σ) i)) (V₀ i))
variable (p:Satin.PairIdx Y s i k)(u:Beyond P ℓ σ z)
include p hx
lemma lift_room (j:Booth I η):AtSupport false (offsetMask (grantRadius P ℓ z) (chassis η (heel (Vale.apt (Y.ir i) P.block P.R.L s) ∘ σ) j)) (ascender Y s i k (V₀ j)):= (weight Y i k p 0 (hx j)).mono (padding ..) -- implicit args tune
include u
lemma layout_ascent (l:List (Booth I η)) (e:distinctHost l): ascender Y s i k (l.map V₀).prod= (l.map (ascender Y s i k ∘ V₀)).prod:=by
 induction l with
 | nil=> exact ascendUnit Y s i k p
 | cons j l h=>
    obtain ⟨h',v⟩:= (bottom_host ..).1 e; let S':=l.toFinset.biUnion (fun i=>offsetMask z ((σ0) i))
    rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons]; refine (ascendSep Y s i k p (hx j) (receipt_word hx l (S:=S') ?_) ?_).trans (congrArg (_* ·) (h v)) -- tune whitespace block
    · intro i x z y; exact mem_biUnion.mpr ⟨i,List.mem_toFinset.mpr x,y⟩
    intro x w y t; unfold S' at t; obtain ⟨j',h,k⟩:=mem_biUnion.mp t; exact beyond_pay Y i u _ _ (h' j' (List.mem_toFinset.mp h)) w k
variable (V₁: Booth I η→ Mark (P.Ctor (Y.ir i) (s+1))) (b0:ℕ)(bV:∀ j,AtSupport false (offsetMask b0 ((chassis η (heel (Vale.apt (Y.ir i) P.block P.R.L s) ∘ σ)) j)) (V₁ j))(hz:b0 ≤ grantRadius P ℓ z)
variable (C₁:Finset (Booth I η))
omit p u hx
def hybrid (j:Booth I η):Mark (P.Ctor (Y.ir i) (s+1)):= if j∈ C₁ then ascender Y s i k (V₀ j) else V₁ j
local notation "G0"=> (Y.voyage i).CapeT s
local notation "Ωμ"=> city (P.Ctor (Y.ir i) s)
lemma commuteMark {N:Side}(S T:Support (More N))(F X:Mark N)(p:AtSupport false S F)(q:AtSupport false T X)(d:Disjoint S T): Commute F X:=by unfold Commute SemiconjBy; funext v; exact Contact.commAux ((p.allV v).sector) ((q.allV v).sector) d
-- leave generic proposition.
lemma strips {J:Type}[Fintype J][LinearOrder J] (C:Finset J){X:Type*}[Monoid X](G F:J→ X)(l:List J) (q:l.Pairwise fun i j=> Commute (F i) (G j)): ((Leit C l).map G).prod * ((Leit (univ \ C) l).map F).prod=(l.map fun i=> if i∈C then G i else F i).prod:=by
 induction l with
 | nil=> simp [Leit]
 | cons i l ih=>
    obtain ⟨w,t⟩:= List.pairwise_cons.mp q
    by_cases s:i∈ C; · rw [List.map_cons,List.prod_cons,if_pos s,←ih t]; simp [Leit,s,mul_assoc]
    let x:=F i; let P:=((Leit C l).map G); rw [List.map_cons,List.prod_cons,if_neg s,←ih t]; have hv(i':List J)(u:∀ j∈i',Commute (F i) (G j)): Commute x (i'.map G).prod:=by
        induction i' with
        | nil=> exact Commute.one_right _
        | cons j r h=> exact (u j (List.mem_cons_self ..)).mul_right (h (fun j u'=>u j (List.mem_cons_of_mem _ u')))
    have eq:= (hv (Leit C l) (fun j f=>w j (List.mem_filter.mp f).1)).symm.eq
    rw [show Leit C (i::l)=Leit C l from (by simp [Leit,s]), show Leit (univ \ C) (i::l)=i::Leit (univ \ C) l from (by simp [Leit,s]),List.map_cons,List.prod_cons]; change P.prod*(x*_)=x*(P.prod*_); rw [←mul_assoc, eq, mul_assoc]
lemma cr_mono {N:Side}(t:Site N){a b:ℕ}(h:a≤ b): offsetMask a t ⊆ offsetMask b t:= Corona.halo_mono h le_rfl
include p u hx bV hz
set_option maxHeartbeats 460000
-- packing order here matters: genuine parent touch carried first. Then commute against indicator.
lemma sellRoom (j:Booth I η): AtSupport false (offsetMask (grantRadius P ℓ z) ((σ1) j)) (hybrid (s:=s) (i:=i) (k:=k) Y V₀ V₁ C₁ j):=by
 by_cases h:j∈ C₁
 · rw [hybrid,if_pos h]; exact lift_room Y σ V₀ hx p j
 rw [hybrid,if_neg h]; exact (bV j).mono (cr_mono _ hz)
lemma layoutHybrid (l:List (Booth I η))(w:distinctHost l): ascender Y s i k ((Leit C₁ l).map V₀).prod * ((Leit (univ \ C₁) l).map V₁).prod = (l.map (hybrid (i:=i) (s:=s) (k:=k) Y V₀ V₁ C₁)).prod:=by
 let v:=beyond_pair (heel_range Y i u) l w
 rw [layout_ascent Y σ V₀ hx p u _ (subhost C₁ l w)]; refine strips C₁ (ascender Y s i k ∘ V₀) V₁ l ?_; refine List.Pairwise.imp ?_ v; intro j j' π; exact commuteMark (offsetMask Ru ((σ1) j)) (offsetMask Ru ((σ1) j')) (V₁ j) (ascender Y s i k (V₀ j')) ((bV j).mono (cr_mono _ hz)) (lift_room Y σ V₀ hx p j') π
lemma replantMoment
  (Xp:List (Booth I η)→Orbit (P.Ctor (Y.ir i) (s+1))→ Phys (P.Ctor (Y.ir i) (s+1))) (z':Booth I η→phy (P.Ctor (Y.ir i) s))(g:∀ j,Contact ((Y.voyage i).CapeT s) (offsetMask z (chassis η σ j)) (V₀ j) (z' j))
  (x:∀ l,distinctHost l→ Version (city (P.Ctor (Y.ir i) (s+1))) (Xp l))
  (y:∀ (l:List (Booth I η)), distinctHost l→∀ (S:Support (More (P.Ctor (Y.ir i) (s+1)))) (F:Mark (P.Ctor (Y.ir i) (s+1))),AtSupport false S F→ (∀ j∈l,Disjoint S (offsetMask b0 ((σ1) j)))→ markedRead F ((Y.voyage i).CapeT (s+1)) (Xp l) = mark_cost Y i k (s+1) (F*(l.map V₁).prod))
  (l:List (Booth I η))(w:distinctHost l): let f:=fun x:Orbit (P.Ctor (Y.ir i) s)=> beamZ Λ (acts (((Leit C₁ l).map fun j=> z' j x).prod) (carryStep Y i k (Xp (Leit (univ \ C₁) l)) x)); Integrable f Ωμ∧ (∫ x,f x∂ Ωμ )= mark_cost Y i k (s+1) (l.map (hybrid (i:=i) (s:=s) (k:=k) Y V₀ V₁ C₁)).prod:=by
 let L:=Leit C₁ l; let L':= Leit (univ \ C₁) l; let F:= (L.map V₀).prod; let T:=fun i=> offsetMask Ru ((σ1) i); let U:Support (More Λs):= L.toFinset.biUnion T -- order
 have d:= x L' (subhost (univ \ C₁) l w); have ht:AtSupport false univ F:= receipt_word hx _ (fun i _=>Finset.subset_univ _); let ζ₁:=carryStep Y i k (Xp L')
 intro f; rw [show f=(fun x:Orbit Λ=> letterRead (F (x.1, G0 x)) (ζ₁ x)) from funext fun z=> (Contact.stencil g (beyond_pair u L (subhost C₁ l w)) z (ζ₁ z)).symm]
 refine ⟨(phaseStep Y i k p d).letterpay ((Y.voyage i).ownership s).paid.bill ht.env, (kayStep Y i k p d F ht).trans ?_⟩
 rw [y _ (subhost (univ \ C₁) l w) U]
 · exact congrArg _ (layoutHybrid Y σ V₀ hx p u V₁ b0 bV hz C₁ _ w)
 · rw [layout_ascent Y σ V₀ hx p u _ (subhost C₁ l w)]; exact receipt_word (fun j=> lift_room Y σ V₀ hx p j) L (fun i w x h=> mem_biUnion.mpr ⟨i,List.mem_toFinset.mpr w,h⟩)
 intro j hj; have r:= beyond_pair (heel_range Y i u) l w; apply Finset.disjoint_left.mpr; intro g' s0 e; unfold U at s0; obtain ⟨t,ht,h⟩:=mem_biUnion.mp s0; have sT:t∈L:=List.mem_toFinset.mp ht; have v:t≠ j:=by
    intro k'; apply (Finset.mem_sdiff.mp (of_decide_eq_true (List.mem_filter.mp hj).2)).2; exact k' ▸ of_decide_eq_true (List.mem_filter.mp sT).2
 let _ : Std.Symm (fun i j : WK=> Disjoint (T i) (T j)) := ⟨fun _ _ h=> h.symm⟩; exact Finset.disjoint_left.mp ((show l.Pairwise (fun i j=> Disjoint (T i) (T j)) from r).forall (List.mem_filter.mp sT).1 (List.mem_filter.mp hj).1 v) h (cr_mono _ hz e) -- membership
#print axioms replantMoment
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
