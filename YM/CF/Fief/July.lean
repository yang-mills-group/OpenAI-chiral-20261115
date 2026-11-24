import YM.CF.Fief.Tin
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open YM.Push.AbsoluteSums
variable {n k:ℕ} {f N B:Side} {a b d C C' K K':ℝ}
local notation "Q"=> Domain N B
open Lich.Muster
section mass
variable (G:Ratio (Domain N B) f)(s:Signed)(v x:ℕ)
def spark (Z:ℕ→RG.Atom SU.group n)(i:Site f ×ℕ):Palot.leaf (Site (Domain N B)):= Lich.Muster.parcel (fun j=> s.act (G.parent j)) v i.1 (Z i.2)
variable {W:ℕ→RG.Atom SU.group n}{D τ:ℝ}
lemma cutM(z:ℕ)(i: Site f) : (spark G s (v*x) W (i,z)).val=(Footprint.enlargement G v x (Paths.bundle i (W z).leg)).image s.actEquiv.toEquiv:=by
 unfold Footprint.enlargement; have ht:i∈Paths.bundle i (W z).leg:=mem_insert_self ..; change Lattice.halo _ _ =_; rw [← Push.Local.halo_map _ (fun i j=>separation_signed i j s)]; apply congrArg (Lattice.halo (n:=Domain N B) (v*x)); rw [Paths.atom_foot,Finset.insert_eq_of_mem ht, Finset.image_image]; rfl -- tune
lemma may (p: SumBudget (fun i=>(W i).budget (C+τ)) K) (h:Footprint.reserve C a (Paths.legFee G v x) d)(hv:0 ≤ τ)(hC:0<C)(hk:0 < x) (b:ℝ)(u:0≤b)(i:Site (Domain N B)): SumBudget (fun k:Site f ×ℕ=> tallyL i (spark G s (v*x) W k) a x*(b*(W k.2).budget τ)) (Footprint.payment (G.count.val^4) (Paths.originFee v x) 0 d b K a (Paths.baseFee (d:=n) G v)):=by
 let Z(i:ℕ):= (W i).leg; let F(y:Site f×ℕ):= Footprint.enlargement G v x (Paths.bundle y.1 (Z y.2)); let g(i:ℕ):= (W i).budget τ; let q:=s.actEquiv (R:=Per (Domain N B)); have hm(i:ℕ):0 ≤ g i:=by unfold g RG.Atom.budget RG.Atom.magnitude; positivity
 have hp(k:ℕ):g k*Real.exp (C*Paths.length (Z k))=(W k).budget (C+τ):=by unfold g RG.Atom.budget; rw [mul_assoc,← Real.exp_add,add_mul]; unfold Z Paths.length RG.Atom.length; rw [add_comm (τ*_)]
 have hx(y:Site f ×ℕ): (if q.symm i∈ F y then b*g y.2 *Real.exp (a*coverNumber x (F y)) else 0)=tallyL i (spark G s (v*x) W y) a x*(b*(W y.2).budget τ):=by
    unfold tallyL; rw [show (spark G s (v*x) W y).val=(F y).image q.toEquiv from cutM ..,Push.Local.cover_map _ _]; swap; · exact fun i j=> separation_signed i j s
    have he(p:Support (Domain N B)): i∈ p.image q.toEquiv↔ q.symm i∈ p:=?_; swap
    · rw [Finset.mem_image]; constructor; rintro ⟨k,h,z⟩; rw [←z]; change q.symm (q k)∈p; rw [q.symm_apply_apply]; exact h; intro t; exact ⟨_,t,q.apply_symm_apply i⟩ -- tune orientation
    simp_rw [he]; split; · unfold g; ring
    simp
 simp_rw [←hx]; simpa only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] using Paths.bundle_hit G v x Z g hC hm (by simp_rw [hp]; exact p) F (fun _=>Subset.refl _) hk u h 0 (fun k=> b*g k.2) (fun i=>mul_nonneg u (hm ..)) (fun _=>by rw [pow_zero,mul_one]) 0 (q.symm i)
end mass
section coin
variable{w:ℝ}{c:Side}
variable {i:Palot.leaf (Site (Domain N B))}
lemma offsetY (L:ℕ→ Palot.leaf (Site Q)){f:ℕ→ℝ}(h:Summable f) : Summable (fun k=> if L k=i then f k else 0):= by rw [show (fun k=> if L k=i then f k else 0) = {k|L k=i}.indicator f from ?_]; exact h.indicator _; ext; simp [Set.indicator]
lemma penny (s:ℕ→ Palot.leaf (Site Q)){F:ℕ→ℝ}{x:Site Q}{r:ℕ}{v:ℝ}(h:Summable F): ∑ i, tallyL x i v r * (Lich.Muster.crop i s F)=∑' i:ℕ, tallyL x (s i) v r*F i:=by
 unfold Lich.Muster.crop; simp_rw [←tsum_mul_left]
 rw [←Summable.tsum_finsetSum (fun i _=> Summable.mul_left (tallyL x i v r) (offsetY s h))] -- order
 refine tsum_congr fun z=>?_ ; simp
lemma marine {u:ℝ}{m:ℕ} {Y:Site f ×ℕ→ Palot.leaf (Site Q)} (F:ℕ→ℝ)(x:Site Q)(p:Summable F)(q:SumBudget (fun i:Site f ×ℕ=> tallyL x (Y i) u m* F i.2) K) : ∑ i, tallyL x i u m*(∑ j:Site f, Lich.Muster.crop i (fun h=>Y (j,h)) F)≤ K:=by
 simp_rw [mul_sum]; rw [sum_comm]; simp_rw [penny (x:=x) (v:=u) (r:=m) (fun k=>Y (_,k)) p]; have he:= q.2.1.tsum_prod; conv_rhs at he => rw [tsum_fintype]
 exact he.symm.le.trans q.2.2
variable {V:ℕ→RG.Atom SU.group n}
lemma loan (q:SumBudget (fun i=>(V i).budget (a+b)) K)(hp:0 ≤ a): Summable (fun i=>(V i).budget b):= Summable.of_norm_bounded q.2.1 (fun i=>by
    have hv:0 ≤ (V i).budget b:= by unfold RG.Atom.budget RG.Atom.magnitude; positivity
    rw [Real.norm_of_nonneg hv]; unfold RG.Atom.budget RG.Atom.magnitude; gcongr ; linarith) -- tune
lemma swift(G:Ratio (Domain N B) f)(l n':ℕ)(s:Signed) (p: SumBudget (fun i=>(V i).budget (C+b)) K)(h: Footprint.reserve C a (Paths.legFee G l n') d)(hp:0≤b)(hx:0<C)(ht:0<n')(u:ℝ)(hz:0≤u)(x:Site (Domain N B)): (∑ i, tallyL x i a n'*(∑ j:Site f,Lich.Muster.crop i (fun z=> spark G s (l*n') V (j,z)) (fun z=>u*(V z).budget b)))≤ Footprint.payment (G.count.val^4) (Paths.originFee l n') 0 d u K a (Paths.baseFee (d:=n) G l):=marine _ x ((loan p hx.le).mul_left _) (may G s l n' p h hp hx ht u hz x) -- order
lemma ope {x:ℕ→ℝ}(p:∀ i,0≤ x i)(L:ℕ→ Palot.leaf (Site Q)) :0≤Lich.Muster.crop i L x:=tsum_nonneg (fun i=> by split; exact p _; rfl) -- tune
end coin
end YM.CF.Fief
