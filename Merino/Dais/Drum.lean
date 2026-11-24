import Merino.Dais.Call
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Dais
open YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise

variable {I:Type}[LinearOrder I][Fintype I]
variable {N P B n:Side}
variable {L:Side}
variable (G:Ratio (mid N B) (mid P B))
variable (X:GramM (mid N B))(Y:GramM (mid P B))
variable (o:I→Site (mid N B))
local notation "FINE" => mid P B
local notation "GRAFT" => mid N B
local notation "vFine" => Hove.heel G ∘ o

structure Bands (b f L:ℕ):Prop where
 height:3*L≤f
 harp:f^3+f≤L*(b^3+b)
 tip:(L+1)*(4*b+2)+2*b ≤ b+b^3
lemma bigger (d:ℝ) (k:ℕ)(hk:3≤k):
 ∀ᶠ x:ℝ in atTop, Bands (radiusB x) (radiusB (x+d)) k:=by
 have q:Tendsto (fun x=>x+d) atTop atTop:= tendsto_atTop_add_const_right atTop d tendsto_id
 have w:=Work.E01.radiusB_tendsto
 filter_upwards [(w.comp q).eventually_ge_atTop (3*k),w.eventually_ge_atTop (9*k+10),eventually_ge_atTop (max 2 d),q.eventually_ge_atTop 2,Real.tendsto_log_atTop.eventually_ge_atTop 100] with x a b c v j

 have e:Real.log (x+d)≤ Real.log x+2:=by
    calc
     _ ≤ Real.log (x*2) := Real.log_le_log (by linarith only [v])
          (by linarith only [(max_le_iff.mp c).2])
     _ ≤ _ := by rw [Real.log_mul (by linarith only [(max_le_iff.mp c).1]) (by simp)]
                 linarith [Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]
 have he:=pow_le_pow_left₀ (Real.log_nonneg (show 1≤x+d by linarith only [v])) e 2
 let t:=radiusB (x+d); let r:=radiusB x
 have hp:4*t≤5*r:=by
   have hm:Real.log x^2 ≤ (r:ℝ):=Nat.le_ceil _
   have hn:(t:ℝ)<Real.log (x+d)^2+1:=Nat.ceil_lt_add_one (sq_nonneg _)
   exact_mod_cast (show 4*(t:ℝ) ≤ 5*(r:ℝ) by nlinarith [mul_self_nonneg (Real.log x-10)])
 refine ⟨a,?_,?_⟩
 · have hc:=Nat.pow_le_pow_left hp 3
   rw [mul_pow,mul_pow] at hc
   refine le_trans (show t^3+t≤3*(r^3+r) from ?_)
             (Nat.mul_le_mul_right _ hk)
   linarith only [hc,hp,Nat.zero_le (r^3),Nat.zero_le r]
 change _*(4*r+2)+2*r ≤ r+r^3
 change 9*k+10≤r at b
 nlinarith [mul_le_mul_right b r,Nat.le_self_pow (by decide : 2≠0) r,show r^2≤r^3 by gcongr <;> omega]

section
variable {α:Side} {b c u:ℕ}
lemma transported
 (e:Odd G.count.val)
 (t:Bands b c G.count.val)
 (z:Force_M b (node ∘ o) u):
 GapN o b G.count.val u ∧ Force_M c (node ∘ vFine) u:=by
 have hG(i:I):node (vFine i)= (Rush.ratio G).embed (node (o i)):=by
     simp only [Function.comp_apply]
     unfold heel
     rw [embed_node G e]; simp
 have q:Apex (cape_B c) c (node∘vFine):=by
   intro i j h
   simp only [comp_apply] at hG
   simp only [comp_apply,hG] at h ⊢
   rw [Laic.emptio]
   have he:=z.1 i j (show (node ∘ o) i ≠ (node∘o) j from fun u=>h (congrArg _ u))
   refine lt_of_le_of_lt ?_ (Nat.mul_lt_mul_of_pos_left he (Rush.ratio G).count.property)
   change c^3 + c^3 + c + c ≤ G.count.val*(b^3 + b^3 + b + b)
   have u:=t.harp
   linarith only [u]
 refine ⟨fun y=>?_,q,fun y=>?_⟩
 · exact le_trans (card_le_card fun i l=>
       mem_filter.mpr ⟨mem_univ _, (separation_comm ..).trans_le
         ((mem_filter.mp l).2.trans t.tip)⟩) (z.2 y)
 let f:=node∘ vFine
 let a:=reach_B (cape_B c) c f y
 by_cases d:a.Nonempty
 · obtain ⟨i,r⟩:=d
   refine le_trans (card_le_card ?_) (z.2 (node (o i)))
   intro j l
   have hf:f i=f j:=by
     by_contra e'
     have v:=q i j e'
     have w:=separation_triangle (f i) y (f j)
     rw [separation_comm (f i) y] at w
     have p:separation y (f i) ≤ c+cape_B c:=(mem_filter.mp r).2
     have p':separation y (f j) ≤ c+cape_B c:=(mem_filter.mp l).2
     change _ < separation (f i) (f j) at v
     omega
   have r:node (o i)=node (o j):= (ratio G).embed_injective
        ((hG i).symm.trans (hf.trans (hG j)))
   apply mem_filter.mpr
   exact ⟨mem_univ _,by rw [Function.comp_apply,r,separation_self];omega⟩
 change a.card≤u
 rw [Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp d)]
 omega

lemma proximity (e:Odd G.count.val)
 (t:Bands b c G.count.val) (x:Skye.Seat FINE):
 ∃ v, separation (node (heel G v)) x≤c:=by
 refine ⟨pew (G:=G) x,?_⟩
 let v:=pew (G:=G) x
 have l:node (heel G v)= (ratio G).embed (node v):=by unfold heel;rw [embed_node G e]; simp
 change separation (node (heel G v)) x≤c
 rw [l]
 exact (peep ..).trans t.height

end

open Buffered Afterglow Tower.VacuumSelection
open Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation


/-- Hence apply at Bands on all Force_M coarse spacings, which include singles.
 For arbitrary boxes one asks whether the coarse root is the one from proximity
 or otherwise near enough — no restriction for the actual fixed single Y. -/
lemma sounding (P:Spine):
 ∀ᶠ s in atTop,∀ i k, s<P.run.uv k→
   Bands (LedgerM P s i k).p.B (LedgerM P (s+1) i k).p.B
    (climbRatio P s i).count.val ∧
    (climbRatio P s i).count=P.par.R.L∧Odd (climbRatio P s i).count.val:= by
 let d:=Vale.billX P.par.R.L
 filter_upwards [(turnover P.par).eventually
    (bigger d P.par.R.L.val P.par.R.coarse)] with s e i k p
 refine ⟨?_,rfl,P.par.R.odd_side⟩
 change Bands (Papal.gram _ _ _ _).p.B (Papal.gram _ _ _ _).p.B _
 rw [(Papal.prices_plot _ _ _ _ p.le).1,(Papal.prices_plot _ _ _ _ p).1]
 rw [(P.run.meter.boot s).2.1,(P.run.meter.boot (s+1)).2.1]
 rw [hat_step]; exact e

end YM.CF.Merino.Dais
