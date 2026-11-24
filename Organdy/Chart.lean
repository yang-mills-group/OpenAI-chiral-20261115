import Organdy.Roast
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste.Clock
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye CF.Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open Buffered.Afterglow
open Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m:Side}{j r p d t:ℕ}{M:Tulip.Male}{ε ξ σ C D:ℝ}
namespace Hookah.Rake
open Regis.Head Etch Regis.Head.Garland
open scoped Classical
open Scree

open Organdy Optic Scree Push.Local
-- Bose probes
variable {W:Pane N→ℂ} {z o: Seat N} {s:Signed}{w : ℕ} {x a:ℝ}

open Larva (Domaine Chip)
open Gleam BProof
open Next.Rank.Spindle
open Pressure Worth
variable {A:Organdy.Ink (Chip (More N))}
     {R:Rules SU.group} {ζ b:ℝ}

abbrev portrait (x:ℝ):=1+knock x*(rail x)^2
lemma portfolio (x:ℝ):1≤portrait x:=
 le_add_of_nonneg_right (mul_nonneg (coin_pos ..).le (sq_nonneg _))

section
variable (H:Domaine w ζ (temp x) (stow x) b W A)
 (h:harbor R ζ b x)(a₀:|a|≤knock x)
include H h a₀
lemma shrub (g:Bool)(s:Signed)(o z:Seat N)(U:Pane N) :
 ‖(a:ℂ)* pom g (cistern x W z s o U)‖ ≤ knock x*rail x^2:=by
 rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,show ∀ y, ‖pom g y‖=‖y‖ from by intro y; cases g<;> simp [pom]]
 exact mul_le_mul a₀ (cistern_rate H h ..) (norm_nonneg _) (coin_pos ..).le

lemma Broach.early {B:Hookah N}(y:Broach W z w x a B)(U:Fields N): ‖B.x U‖≤portrait x:=by
 obtain ⟨s,o,f,g,_⟩:=y.income
 rw [g,bootM,norm_smul,norm_one,mul_one,pop]
 exact (norm_add_le ..).trans (add_le_add (norm_one.le) (shrub H h a₀ _ _ _ _ _))

lemma Sown.rain {L:List (Hookah N)} (v:Sown W z w x a p L)(U:Fields N):‖buffet L U‖≤portrait x^L.length:=by
 induction L with
 | nil=>simp [Hookah.buffet]
 | cons i L ih=>
    rw [List.length_cons,pow_succ',buffet_more,Pi.mul_apply]
    exact (norm_mul_le ..).trans (mul_le_mul (Broach.early H h a₀ (v.core i List.mem_cons_self) U)
        (ih ⟨fun i t=> v.core i (List.mem_cons_of_mem _ t), (List.pairwise_cons.mp v.annex).2⟩) (norm_nonneg _) (zero_le_one.trans (portfolio x)))

lemma primrose(g:Bool)(s:Signed)(o z:Seat N)(U:Pane N) :
 ‖pop x W z a s o g U‖ ≤ Real.exp (a*(cistern x W z s o U).re+tithe x):=by
 let y:ℂ:=a*pom g (cistern x W z s o U)
 have p:y.re=a*(cistern x W z s o U).re:=by unfold y; cases g<;>simp [pom]
 have v:=pow_le_pow_left₀ (norm_nonneg _) (shrub H h a₀ g s o z U) 2
 rw [mul_pow, ←pow_mul] at v
 refine (le_trans ?_ (Real.exp_monotone (by gcongr : y.re + ‖y‖^2 ≤ y.re+tithe x))).trans_eq (by rw [p])
 refine (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).1 ?_
 rw [sq (Real.exp _),←Real.exp_add]
 apply le_trans _ (Real.add_one_le_exp _)
 change ‖1+y‖ ^ 2 ≤ _
 rw [Complex.sq_norm,Complex.normSq_add,Complex.sq_norm]; simp; nlinarith [Complex.normSq_nonneg y]


lemma Sown.pollen {L:List (Hookah N)}(v:Sown W z w x a p L) :
 ∃ (D:Ballroom (Fin L.length) (More N))(U:Pane N→ℂ), D.Space w z ∧
 (∀ y:Fields N, Hookah.buffet L y=U y.1 • 1) ∧
 ∀ i:Pane N, ‖U i‖≤ Real.exp (a*nectar x W z D i+L.length*tithe x):=by
 let T:= Fin L.length; let Z(i:T):=L.get i; have hp(i:T):= (v.core _ (List.get_mem L i)).income
 choose s o g f h' using hp
 let D:Ballroom (Fin L.length) (More N):=⟨s,o⟩
 have hf {i j:T}(t:i<j): Disjoint (D.area w z i) (D.area w z j) :=Finset.disjoint_left.mpr fun {y} u b=> by
    have m:=v.annex.rel_get_of_lt t y (h' i u) y (h' j b)
    rw [separation_self] at m; omega
 let A'(j:T)(y:Pane N):=pop x W z a (s j) (o j) (g j) y
 refine ⟨D,fun i=>∏ j:T,A' j i,fun i j k=> (lt_or_gt_of_ne k).elim hf (fun v=> (hf v).symm),?_,fun i=>?_⟩
 · intro y; apply buffet_head (z:=fun j=>A' j y.1)
   intro i; rw [f i]; rfl
 rw [norm_prod]

 refine (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> primrose H h a₀ (g j) (s j) (o j) z i)).trans_eq ?_
 rw [←Real.exp_sum,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,← mul_sum]
 unfold T at *
 rw [Fintype.card_fin]
 rfl
end

abbrev hatch {N:Side}(w:ℕ)(z:Seat N):=Lattice.halo (w+2) {(0:Seat N),z}
abbrev zoopN (w:ℕ)(x:ℝ)(W:Pane N→ℂ)(z:Seat N)(a:ℝ):Hookah N:=
 ⟨1+(a:ℂ) • markPair x W z,hatch w z,0⟩
lemma atHome (H:Domaine w ζ (temp x) (stow x) b W A)
 (h:harbor R ζ b x)(z: Seat N): AtSupport false (hatch w z) (markPair x W z):=by
 refine ⟨⟨?_,(rail x)^2, ?_⟩,?_,?_⟩
 · exact ((cistern_meas H.meas ..).comp measurable_fst).smul measurable_const
 · intro t
   simp only [markPair,norm_smul,norm_one,mul_one]
   exact cistern_rate H h ..
 · intro i j f _
   have v (s: Signed) (o:Seat N)(g:o∈({0,z}:Finset (Seat N))) :
           wares x W s o i.1=wares x W s o j.1:=by
      unfold wares
      have p: Agrees (Lattice.halo w {(0:Seat N)}) (Lattice.pull s o i.1) (Lattice.pull s o j.1):=by
         apply agrees_pull; rw [silo]
         apply agrees_mono f
         intro d e

         have l:separation o d≤w:=by simpa [halo_spec] using e
         exact halo_spec.mpr ⟨_,g,(l.trans (by omega: w≤w+2))⟩
      rw [H.loc _ _ p]
   unfold markPair cistern
   rw [v 1 0 (by simp), v _ _ (by simp [affine])]
 · intro t
   exact Fine.one.scale _

lemma zoom (H:AtSupport false (hatch w z) (markPair x W z)):
    Broach W z w x a (zoopN w x W z a):=by
 refine ⟨(AtSupport.oneM _).addM (H.smulM _), 1,0,false,?_,?_⟩
 · funext U
   change 1+(a:ℂ)•(cistern x W z 1 0 U.1 • (1:FC _))=(1+(a:ℂ)*cistern x W z 1 0 U.1) • _
   rw [add_smul,one_smul,mul_smul]
 · simp [zoopN,hatch,affine]
