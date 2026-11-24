import Palm.Transfer
set_option maxHeartbeats 1100000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x : ℝ}
  {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ→ℝ) {N0 : ℕ} (T : Month x 1 6 2 N0 V W) (ht : T.q ≤ m.val)
  (S : Cape m B R.L) (ρ : ℕ→ℝ) (f : ℕ→ℝ) (k i : ℕ)
namespace Parcel
open Roots Mew Tune Oath Bake Neon
attribute [-instance] instDecidableEqLex
variable {I:Type}[Fintype I][LinearOrder I]
local notation "Ψd"=>LabelΩ I
-- fixed σ= tiβ and block linear matrices telescope
local notation "ξκ"=> (tiβ (I:=I))
lemma anchor (J:I → Site (mid N B))(p: Function.Injective (Cube.node ∘ J))(i:Ψd):pipe_ζ (Cube.node ∘ xΞ J) i=pipe_ζ ξκ i:=by
 ext j; simp only [pipe_ζ, Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨fun a=> p a,congrArg (Cube.node∘ J)⟩
lemma white (J:I → Site (mid N B))(p: Function.Injective (Cube.node ∘ J))(g:Ψd → Ψd → ℂ)(X:List Ψd→ℂ)(l:List Ψd) : Roots.snow (Cube.node ∘ xΞ J) g X l = Roots.snow ξκ g X l:=by
 induction l generalizing X with | nil=>rfl | cons i l ih=> rw [Roots.snow,Roots.snow,anchor J p]; simp_rw [ih]
lemma psiA (J:I → Site (mid N B))(p: Function.Injective (Cube.node ∘ J))(l:List Ψd):ψS ξκ l→ψS (Cube.node ∘ xΞ J) l:=by
 intro t; change (l.map ((Cube.node ∘ J) ∘ ξκ)).Nodup; rw [←List.map_map]; exact List.Nodup.map p t
lemma broad (ι:Ψd)(J:I → Site (mid N B))(p: Function.Injective (Cube.node ∘ J))(C:Ψd→Ψd→ℂ)(Q:ℝ)(v:∀ z∈hill Ψd,∀ i:Ψd,‖toV_C (Cube.node ∘ xΞ J) C z i‖ ≤ Q) : ∑ j∈pipe_ζ ξκ ι, ‖C j ι‖ ≤ (Fintype.card Ξθ:ℝ)*Q:=by
 -- toV_C orientation? broaden via elementwise
 have e (i t:Ψd)(h:t∈pipe_ζ ξκ i) : ‖C t i‖≤Q:=by
   let z : Key Ψd:= fun j=> if j=i then 1 else 0
   -- Key ?
   refine le_of_eq_of_le ?_ (v z ?_ t)
   · unfold toV_C; rw [anchor J p, Finset.sum_eq_single i]; swap
     · intro b m hm; exact (by change C _ _*(if b=i then 1 else 0)=0; rw [if_neg hm,mul_zero])
     swap
     · intro m; exact False.elim (m (Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp h).2.symm⟩))
     change _= ‖_*(if i=i then (1:ℂ) else 0)‖; rw [if_pos rfl,mul_one]
   refine hill_i.mpr fun t' => ?_; change ‖(if t'=i then (1:ℂ) else 0)‖ ≤ 1; split <;> simp
 calc
    _ ≤ ∑ j∈pipe_ζ ξκ ι,Q:= sum_le_sum fun j h=> e ι j h
    _ = _:=by rw [←anchor J p,Py.ΨM J p,Finset.sum_const,card_map,card_univ,nsmul_eq_mul]
-- spar economy: analytic papers may give even Q without card for row or 1-norm using z's phases. $Column vs row. Current acute allows cost C4*L^4.
lemma snowBound (C:Ψd→Ψd→ℂ)(B:ℝ)(X:List Ψd→ℂ)(l:List Ψd)(Q:ℝ)(hb:∀ t:Ψd,∑ j∈ pipe_ζ ξκ t, ‖C j t‖≤B)(a:0≤B)(z:0≤Q)(p:∀ l':List Ψd,l'.map ξκ=l.map ξκ→ ‖X l'‖≤Q): ‖Roots.snow ξκ C X l‖≤ B^l.length*Q:=by
 induction l generalizing X with
 | nil=> simpa only [Roots.snow,List.length_nil,pow_zero,one_mul] using (p [] rfl)
 | cons i L ih=>
    rw [Roots.snow,List.length_cons]; refine (norm_sum_le ..).trans ?_
    rw [pow_succ',mul_assoc]
    calc
      _ ≤ ∑ j∈pipe_ζ ξκ i, ‖C j i‖*(B^L.length*Q):=sum_le_sum fun j h=> by
          rw [norm_smul]; exact mul_le_mul_of_nonneg_left (ih _ (fun l e=> p (j::l) (by rw [List.map_cons,List.map_cons,e,(mem_filter.mp h).2]))) (norm_nonneg _)
      _ ≤ _:=by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hb i) (by positivity)
noncomputable def drift (j:ℕ) (C:ℕ→Ψd→Ψd→ ℂ) (X:List Ψd→ℂ): (a:ℕ)→List Ψd→ℂ
 | 0=> X
 | t+1=> fun l=> Roots.snow ξκ (C (j-(t+1))) (drift j C X t) l
lemma driftCost (j:ℕ) (C:ℕ→Ψd→Ψd→ ℂ) (X:List Ψd→ℂ) (l:List Ψd)(a:ℕ)
    (B Q:ℝ)(u:0≤B)(hu:0≤Q)(hX:∀ t,t.map ξκ = l.map ξκ→ ‖X t‖ ≤ Q)
    (v:∀ i, j-a ≤ i→ i<j → ∀ d:Ψd,∑ k∈pipe_ζ ξκ d,‖C i k d‖ ≤ B)(p:a ≤ j):
    ‖drift j C X a l‖ ≤ (B^l.length)^a*Q:=by
 induction a generalizing l with
 | zero=>unfold drift; rw [pow_zero,one_mul]; exact hX l rfl
 | succ a ih=>
    rw [drift, pow_succ',mul_assoc]; apply snowBound _ _ _ _ _ (v _ le_rfl (by omega)) u (by positivity)
    intro l' h; have q:= ih l' (fun t s=>hX t (s.trans h)) (fun i x y=>v i (by omega) y) (by omega); rwa [show l'.length=l.length by simpa only [List.length_map] using congrArg List.length h] at q
end Parcel
end YM.CF.Py.Rate
