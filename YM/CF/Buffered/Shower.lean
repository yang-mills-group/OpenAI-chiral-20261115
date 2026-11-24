import YM.CF.Buffered.Sidings
/-!
# Haar pressure gather. Measure preserving for these rail fields.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m v p B n w:Side}{δ:Axis→Side}{i:Axis}{ζ:TStem i}
variable (V:Traversed ζ δ n)
local notation "N" => n.val
local notation "X" => Wet ζ v B
local notation "C" => Car ζ
local notation "S" => Domain v B
local notation "b" => GridN v

section pi
variable {I J Y:Type*}[Fintype I][Fintype J][MeasurableSpace Y]
lemma unc_mp (μ:Measure Y)[IsProbabilityMeasure μ]:
 MeasurePreserving (fun x:I→ J→Y=> uncurry x) (Measure.pi (fun _ : I=> Measure.pi fun _=> μ)) (Measure.pi fun _=> μ):=by
 let T:=fun x:I→J→Y=> uncurry x; have h : Measurable T:= measurable_pi_lambda _ fun i=> (measurable_pi_apply _).comp (measurable_pi_apply _); refine ⟨h,Eq.symm (Measure.pi_eq ?_)⟩ -- tune
 intro s hs; rw [Measure.map_apply h (MeasurableSet.univ_pi hs)]; rw [show (fun x:I→J→Y=> uncurry x) ⁻¹' Set.univ.pi s=Set.univ.pi (fun i=> Set.univ.pi (fun j=> s (i,j))) from ?_,Measure.pi_pi]; simp_rw [Measure.pi_pi]; rw [Fintype.prod_prod_type]; ext x; simp [Set.mem_pi,uncurry]
end pi

def fluid (ζ:TStem i)(v B:Side): Measure (Wet ζ v B):=(Measure.pi (fun _=> SU.group.probHaar)).prod (Measure.pi fun _=>cloud)
instance (ζ:TStem i)(v B:Side): IsProbabilityMeasure (fluid ζ v B):= by unfold fluid; infer_instance
local notation "ψ" => fluid ζ v B
local notation "μ" => Measure.prod (piN n.val (fluid ζ v B)) (piN n.val (fluid ζ v B))
local notation "ρ" => Rails.law δ v B

def jewel (p:Bool)(x:X) := if p then shell x else x
lemma invPres : MeasurePreserving (shell (ζ:=ζ) (v:=v) (B:=B)) ψ ψ:=by
 let J:= (C × Post S) × Axis; let d:= C × Post b
 let W:(C × Post S)×Axis→(C × Post S)×Axis:=fun i'=>((i'.1.1,rear {i'.2} i i'.1.2),i'.2)
 let G:C × Post b→ C × Post b:= fun j=> (j.1,rear ∅ i j.2); have hp: Involutive W:= by intro i; unfold W; simp only [rear_mirror]
 let R: J ≃ J :=⟨W,W,hp,hp⟩; have ht:Involutive G:=by intro i; unfold G; simp only [rear_mirror]
 let Q:=RP.ux; let E0:= Measure.pi (fun _:J=> Q); have he: MeasurePreserving (fun x:J→E=> x∘W) E0 E0:= Ordered.reEnd R Q
 let g (j:(C × Post S) × Axis) (x:E):= invertP (i=j.2) x
 have hv: MeasurePreserving (fun x:J→E=> (fun j=> g j (x j))) E0 E0:= measurePreserving_pi _ _ (f:=g) (by intro j; unfold g invertP; split; exact Measure.measurePreserving_inv _; exact MeasurePreserving.id _)
 exact (hv.comp he).prod (Ordered.reEnd (show d≃d from ⟨G,G,ht,ht⟩) cloud)
lemma jewelPres (t:Bool): MeasurePreserving (jewel (ζ:=ζ) (v:=v) (B:=B) t) ψ ψ:=by unfold jewel; cases t; exact MeasurePreserving.id _; exact invPres

-- Wet seam data provide both boundary surfaces; choose the ones supporting this stripe and then
-- join into full Rails. `a : Bool` orient interior variables independently on each slab, no a priori determinantal orientations.
def chaired (w: Stack.Cell X X)(a:Bool): Stack.Cell X X:= (w.1,jewel a w.2)
def ticketSurf (x y:X):X:= (fun k=> if Lith i {k.2} k.1.2 then x.1 k else y.1 k, fun k=> if Lith i ∅ k.2 then x.2 k else y.2 k)
def strips (a: Fin n.val → Bool) (x:DeckIn N X X): Many N X:= fun i=> ticketSurf (x.1 i) (jewel (a i) (x.2 i))
def patched (u: Many N X): Rails δ v B:= (fun i=> (u (lead V i.1.1)).1 ((tail V i.1.1, i.1.2),i.2),fun i=> (u (lead V i.1)).2 (tail V i.1,i.2))
def scatter (a:Fin n.val → Bool) (x:DeckIn N X X) := patched V (strips a x)
lemma ticket_m : MeasurePreserving (fun x:X×X=> ticketSurf x.1 x.2) (Measure.prod ψ ψ) ψ:=by
 let M:Finset ((C × Post S) × Axis):= univ.filter (fun t=> Lith i {t.2} t.1.2); let K:Finset (C×Post b):= univ.filter (fun t=> Lith i ∅ t.2)
 let μ₁:Measure (Atlas ζ S):=Measure.pi fun _=> RP.ux; let μ₂:Measure (Ledger ζ b):=Measure.pi fun _=>cloud; haveI :IsProbabilityMeasure μ₁:=by unfold μ₁; infer_instance
 haveI:IsProbabilityMeasure μ₂:=by unfold μ₂; infer_instance
 let f(x:X×X):X:= (Sample.patchF M x.1.1 x.2.1,Sample.patchF K x.1.2 x.2.2) -- tune Sample
 rw [show (fun x:X×X=> ticketSurf x.1 x.2)=f from ?_]
 · exact ((RP.patch_mp RP.ux M).prod (RP.patch_mp cloud K)).comp (RP.prod_mix μ₁ μ₂)
 funext x; unfold f ticketSurf Sample.patchF; ext <;> simp [K,M] -- tune
lemma chaired_cont (k:Bool): Continuous fun x:Stack.Cell X X=> chaired x k:= by unfold chaired jewel; cases k <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> fun_prop
lemma scatter_mp (a:Fin N→ Bool): MeasurePreserving (scatter V a) μ ρ:=by
 let E0:= piN N ψ; have ht: MeasurePreserving (strips (ζ:=ζ) (v:=v) (B:=B) a) μ E0:=by
   let e:= (measurePreserving_arrowProdEquivProdArrow X X (Fin N) (fun _=>ψ) (fun _=>ψ)).symm
   -- tune
   exact (measurePreserving_pi (f:=fun t:Fin N=> fun x:X×X=> ticketSurf x.1 (jewel (a t) x.2)) _ _ fun t=> ticket_m.comp ((MeasurePreserving.id ψ).prod (jewelPres _))).comp e
 let μ₁:Measure (Atlas ζ S):=Measure.pi fun _=> RP.ux; let μ₂:Measure (Ledger ζ b):=Measure.pi fun _=>cloud
 haveI :IsProbabilityMeasure μ₁:=by unfold μ₁; infer_instance
 haveI:IsProbabilityMeasure μ₂:=by unfold μ₂; infer_instance
 let J:= C × Post b; let L:Fin N × J≃ Rail δ × Post b:=(Equiv.prodAssoc _ _ _).symm.trans (V.click.prodCongr (Equiv.refl _)); let Q:= (C × Post S) × Axis; let Z:Fin N × Q ≃ (Rail δ × Post S) × Axis:=(Equiv.prodAssoc _ _ _).symm.trans (((Equiv.prodAssoc _ _ _).symm.prodCongr (Equiv.refl _)).trans ((V.click.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _))) -- tune
 exact ((((Ordered.reEnd Z SU.group.probHaar).comp (unc_mp _)).prod ((Ordered.reEnd L cloud).comp (unc_mp _))).comp (measurePreserving_arrowProdEquivProdArrow _ _ (Fin N) (fun _=>μ₁) (fun _=> μ₂))).comp ht
lemma chaired_eval (a:Fin N→Bool)(t:Fin N)(w:Car ζ)(x:DeckIn N X X):
 reel (loc V t w) (scatter V a x)=host (chaired (atCell x t.val) (a t)) w:=by
 dsimp only [chaired,host,reel]; apply Prod.ext
 · funext j p
   dsimp only; rw [scatters V w t p]; simp only [scatter,patched,lead_loc, tail_loc,strips,ticketSurf,selected]; dsimp only [atCell]; simp only [recur, Nat.cast_add,Nat.cast_one, Fin.natCast_self]; have he:= tipHigh (i:=i) p; split_ifs <;> simp_all
 funext j; dsimp only; rw [scatters V w t j]; simp only [scatter,patched,lead_loc, tail_loc,strips,ticketSurf,selected]; unfold atCell; dsimp only; have he:= tipHigh (i:=i) j; split_ifs <;> simp_all [recur]
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.scatter_mp
