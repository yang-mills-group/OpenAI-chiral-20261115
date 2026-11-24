import YM.SU5.FiniteGaugeData.Stent.Chiron
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Stent
set_option linter.unusedSimpArgs false
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Kronecker ENNReal
attribute [local instance] opCStarAlgebra
variable (R:Patch)
set_option quotPrecheck false
local notation "Λ"=> R.L
local notation "J"=> R.J
open Cube Stencil Tenant Tap Tulip Branch Spire Peaks Advance Skye Lifted CF.Stent
variable {x:Cover}
open SU -- More.E
variable {N P:Side}(G:Ratio N P)(p:G.count=R.L)(h:4≤R.L.val) {d:ℕ} (q:LaurentRadius R.J G.count d) (t:2*d < N.val)
local notation "φ"=> ratio G
-- stamp.Pay
abbrev Shadow(R:Patch)(o:Lattice.Order)(V:LinksC): SU.E:= travel V (nodeC (specialM R.L)) (growAge o)
abbrev Bliss(R:Patch):= cash R rune 0
noncomputable def Louvre (R: Patch)(V:LinksC): Op SU.Slot:= (Fintype.card Lattice.Order:ℝ)⁻¹ • ∑ o:Lattice.Order,(matter (Shadow R o V)).val
private lemma WindQ : Rush.wind (0: Site N) (0:Cover)=1:=by
 let p:Site N:=0; have hx:= infT p (0:Cover); simp only [map_zero,add_zero] at hx; have ht:=add_eq_left.mp hx; have hh: periods N (natural p)=0:= (nsmul_right_injective (M:=Cover) N.property.ne' (by simpa only [smul_zero])); change Rush.wind p 0=_; simp only [Rush.wind,add_zero,hh,Rush.fee]; simp
include h
lemma bliss_pay : 0< (Bliss R).re:= price R rune (limit_b _ h)
include q p t
lemma jomo (u:Nom N P)(i j:SpinIdx)(v w:SU.Slot)(o:Lattice.Order) :
  let x: Inta G:= Yr G i; let y:= Yc G j; let D:= tub (brix R.J G.count)
  drag G true false x.2 y.2 0 (D 0 x.2 y.2) o (unionP u) (x,v) (y,w) = (if i=j then Bliss R else 0) * (matter (Shadow R o (onC P u.1))).val v w:=by
 intro x y D; have hh:4≤ G.count.val:=p.symm ▸ h; have ho: Odd G.count.val:= p.symm ▸ R.odd_side
 rw [drag_entry,if_pos (by unfold x y; simp [Yr,Yc])]; change wind x.1 0 * D 0 x.2 y.2 * (matter (travel u.1 (touch G true x) (runD true false G.count x.2 y.2 0 o))).val v w=_; rw [show D 0 x.2 y.2= if i=j then Bliss R else 0 from ?_,show wind x.1 0=1 from WindQ,one_mul]
 · rw [show touch G true x=wrap _ (nodeC (specialM G.count)) from Uport G hh ho i,show runD true false G.count x.2 y.2 0 o=growAge o from run_ae G hh ho _ _ _]; unfold Shadow onC; rw [travel_at,add_zero,p]
 unfold D x y Yr Yc Bliss; dsimp only; rw [p, correspondent R, limit_a R.L h R.odd_side]
-- extraction `mosaic`. min laset unalias.
lemma mosaicQ (u:Nom N P)(i j:SpinIdx)(v w:SU.Slot): let x:=Yr G i; let y:=Yc G j; mosaic G true false (tub (brix R.J G.count)) (unionP u) (x,v) (y,w)=(if i=j then Bliss R else 0) * (Louvre R (onC P u.1)) v w:=by
 intro x y; let D:= tub (brix R.J G.count); let W(o:Lattice.Order)(s r: St G.count)(t:Cover):= drag G true false s r t (D t s r) o (unionP u) (x,v) (y,w)
 have ht(o s r z): W o s r z=0 ∨ (x.2=s ∧ y=(x.1+wrap N z,r)):=by unfold W; unfold D; rw [drag_entry]; split <;> simp_all -- tune
 let L:=LabelSet d; have he: (0:Cover)∈ L:= by rw [show L=LabelSet d from rfl, labels]; unfold Laurent.size; simp
 have hz(o:Lattice.Order):(∑ i:St G.count,∑ j:St G.count,∑ k∈L,W o i j k)= W o x.2 y.2 0:=by
    rw [sum_eq_single x.2,sum_eq_single y.2,sum_eq_single (0:Cover)];
    · intro i v h; refine (ht _ _ _ _).resolve_right ?_; intro e; have hp:= congrArg Prod.fst e.2; apply h; apply covers_H N d t _ v; change (0:Site N)=0+wrap N i at hp; rw [zero_add] at hp; exact hp.symm
    · exact fun h'=> (h' he).elim
    · intro y v p; refine sum_eq_zero fun i u=>?_ ; exact (ht _ _ _ _).resolve_right (fun t=> p (congrArg Prod.snd t.2).symm)
    · intro; simp_all
    · intro x h p; refine sum_eq_zero fun i _=> sum_eq_zero fun j _=>?_ ; exact (ht _ _ _ _).resolve_right (fun t=> p t.1.symm)
    exact fun h=>(h (mem_univ _)).elim
 rw [mosaic_entry G R.J q]; let C (o:Lattice.Order):= matter (Shadow R o (onC P u.1)); let b:ℂ:=if i=j then Bliss R else 0; change ( (Fintype.card Lattice.Order:ℝ)⁻¹ • (∑ o:Lattice.Order,∑ i:St G.count,∑ j:St G.count,∑ k∈L,W o i j k))= b * Louvre R (onC P u.1) v w
 simp_rw [hz,show ∀ o,W o x.2 y.2 0=b*(C o).val v w from fun o=>jomo R G p h q t _ _ _ _ _ _, ←mul_sum]; unfold Louvre; rw [Matrix.smul_apply,Matrix.sum_apply]; simp_rw [Complex.real_smul]; exact mul_left_comm .. -- spelling C( lex reserved
lemma clothZ (u:Nom N P)(i j:SpinIdx)(v w:SU.Slot)(M:Male) : cloth R.J M G (unionP u) (Yr G i,v) (Yc G j,w)=(if i=j then Bliss R else 0) * (Louvre R (onC P u.1)) v w:=by
 rw [cloth_entry, mosaicQ R G p h q t u i j]
 rw [lobe_fine,lobe_fine,lobe_fine,lobe_fine]; by_cases e:i=j; swap; · rw [if_neg e,zero_mul]; simp only [mul_zero,zero_mul,add_zero]
 subst j; by_cases g:i∈ plusHalf <;> simp [Yc,Yr, Fir.angle,Adef.trans raising.symm,cutM,g] -- using `[Adef.trans]` as lemma.
#print axioms clothZ
end YM.CF.Buffered.Stent
