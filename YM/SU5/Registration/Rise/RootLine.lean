import SatinThinRenew
import YM.SU5.FiniteGaugeData.Tower.Baggage
/-!
# Banner geometry with renewal at a much earlier mesh

Control at `markCost` sites by where the *roots* go on a potentially much smaller Side.
Both occupancy & capacity are at the ROOT mesh. That mesh must align with the
length budget issued on the tall-resolution field. Works e.g. with `SatinThinRenew`'s
list of clock sites, or with reflected stencils.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.ClockBooking
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Again CF.Pannier.Chancel
variable {N M:Side}

private lemma far_through_wrap (j:Axis){x y:Seat N}{l u:ℤ}{d:ℕ}(hli:x j=(l:Per (More N)))(hui:y j=(u:Per (More N)))
    (hu:l+(d:ℤ)≤u)(hl:u+(d:ℤ)≤l+(More N).val): d ≤ separation x y:=by
 let B:= N.val
 let w:= u-l; let v:= y-x
 change l+(d:ℤ) ≤ u at hu
 change u+(d:ℤ) ≤ l+ (↑(B*2:ℕ):ℤ) at hl
 have p:v j=(w:Per (More N)):=by unfold w v; rw [Pi.sub_apply, hui,hli, Int.cast_sub]
 rw [separation_comm]; refine le_trans ?_ (component_le v j)
 by_cases h: w ≤ (B:ℤ)
 · have ht: Lattice.lift v j=w:=by
      refine (ZMod.valMinAbs_spec ..).mpr ⟨p,?_⟩
      have hn:0<B:=N.property; change - (↑(B*2:ℕ):ℤ) < w*2 ∧ w*2 ≤ (↑(B*2:ℕ):ℤ); unfold w at *; omega
   rw [ht]; unfold w; omega
 let w':= w-(↑((More N).val):ℤ)
 have ht: Lattice.lift v j=w':=by
    apply (ZMod.valMinAbs_spec ..).mpr; constructor
    · unfold w'; rw [Int.cast_sub]; rw [Int.cast_natCast, ZMod.natCast_self,sub_zero,p]
    have hn:0<B:=N.property; change - (↑(B*2:ℕ):ℤ) < w'*2 ∧ w'*2 ≤ (↑(B*2:ℕ):ℤ); have ht:w'=w- (↑(B*2:ℕ):ℤ):=rfl; unfold w at *; omega
 rw [ht]; have hv:w'=w- (↑(B*2:ℕ):ℤ):=rfl; unfold w at *; omega

structure Packing {α : Type*} (y : α → Mark M) (j:Axis) (N:Side)(a:ℤ) where
 /-- Tracking footprint at N. Can be asymmetric, with orientation. No assertion this alone
 buys thin estimates. -/
 footprint : α → Finset (Seat N)
 turn : ℤ→α→α
 admissible : α→Prop
 still (x:α) (s:ℤ) : admissible x → admissible (turn s x)
 turns (x:α) (s:ℤ) : (footprint x).image ((plane j s).anon N)=footprint (turn s x)
 reflects (x:α) (s:ℤ) : y (turn s x)=reflMark j (a*s) (y x)

variable {α:Type*} {a:ℤ}{y:α→Mark M}{j:Axis}
variable (P:Packing y j N a)
namespace Packing
-- stand in closed interval with interior allowance D (use ℤ throughout shifts)
def NativeRoll (i:Axis)(A:Finset (Seat N))(L R:ℤ) : Prop:=
    ∀ v∈ A, ∃ z:ℤ,L ≤ z ∧ z ≤ R ∧ (z:Per (More N))=v i

structure Stretch (b:Cover)(d D:ℕ)(L R:ℤ)(l:List α) : Prop where
 goal : ∀ x∈ l,P.admissible x
 axial :∀ x∈ l, NativeRoll j (P.footprint x) (L+D) (R-D)
 other :∀ i:Axis, i≠j → ∀ x∈ l, NativeRoll i (P.footprint x) (b i) (b i+d)
 clear :l.Pairwise (fun x y => ∀ u∈P.footprint x,∀ v∈P.footprint y, 2*D ≤ separation u v)
variable {l k:List α}{b:Cover}{L S R:ℤ}{d D:ℕ}
lemma Stretch.weaken {X Y:ℤ}(p:P.Stretch b d D L R l)(hz:X≤L)(hg:R≤Y):P.Stretch b d D X Y l:=by
 refine ⟨p.goal,fun x t v u=>?_,p.other,p.clear⟩
 obtain ⟨A,hx,ht,q⟩:= p.axial x t v u; exact ⟨A,by omega,by omega,q⟩
lemma Stretch.tether (p:P.Stretch b d D L S l)(q:P.Stretch b d D S R k)(x:L≤S)(y:S≤R)(e:R-L≤(More N).val): P.Stretch b d D L R (l++k):=by
 refine ⟨fun a t=>(List.mem_append.mp t).elim (p.goal a) (q.goal a), fun a t=>(List.mem_append.mp t).elim ((p.weaken P le_rfl y).axial a) ((q.weaken P x le_rfl).axial a),fun i u a t=>(List.mem_append.mp t).elim (p.other i u a) (q.other i u a), List.pairwise_append.mpr ⟨p.clear,q.clear,fun x w y t u hx v hy=>?_⟩⟩
 obtain ⟨i,hp,ht,hq⟩:=p.axial x w u hx; obtain ⟨j',iP,hT,hQ⟩:=q.axial y t v hy
 exact far_through_wrap j hq.symm hQ.symm (by omega) (by omega)
lemma Stretch.reflection (s:ℤ)(p:P.Stretch b d D L R l): P.Stretch b d D (2*s-R) (2*s-L) (l.map (P.turn s)):=by
 refine ⟨fun x t=>?_,fun x t v u=>?_,fun i e x t v u=>?_,List.pairwise_map.mpr (p.clear.imp ?_)⟩
 · obtain ⟨x,t',rfl⟩:= List.mem_map.mp t; exact P.still _ _ (p.goal _ t')
 · obtain ⟨x,t',rfl⟩:=List.mem_map.mp t; rw [←P.turns] at u; obtain ⟨v,q,rfl⟩:=mem_image.mp u
   obtain ⟨z,V₀,E,Q⟩:= p.axial x t' v q
   let x':=(plane j s).anon N v; have ht:x' j-(s:Per (More N))=-(v j-(s:Per (More N))):= across_coord ..
   exact ⟨2*s-z,by omega,by omega,by change _=x' j; rw [Int.cast_sub,Int.cast_mul,Q,Int.cast_ofNat,eq_add_of_sub_eq ht]; ring⟩
 · obtain ⟨x,t',rfl⟩:=List.mem_map.mp t; rw [←P.turns] at u; obtain ⟨v,q,rfl⟩:=mem_image.mp u; have he: (plane j s).anon N v i=v i:=by simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,wrap_here,e,e.symm]
   rw [he]; exact p.other i e x t' v q
 intro x y H u X v Y; rw [←P.turns] at X Y; obtain ⟨u,U,rfl⟩:=mem_image.mp X; obtain ⟨v,V,rfl⟩:=mem_image.mp Y
 simp only [Shape.anon,affine,separation_translate,separation_signed]; exact H _ U _ V

lemma mark_turns (l:List α)(s:ℤ): ((l.map (P.turn s)).map y).prod=reflMark j (a*s) (l.map y).prod:=by
 induction l with
 | nil=>exact funext fun _=> (Fock.theta_one _).symm
 | cons q l ih=> simp only [List.map_cons,List.prod_cons,ih,P.reflects]; exact funext fun _=> (Fock.theta_mul ..).symm
end Packing

section plots
-- reconstruct `Stretch` from marker geometry, keep alignment as `a*r` gauge coords
variable {Λ:Preparation}{m':ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus m'))(H:Real.exp 1≤Λ.x)(v i :ℕ)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "Z"=> Journey.side Y i v
local notation "R"=>ruler Λ.block
variable {y':α→Mark (Journey.side Y i v)}
variable (P':Packing y' j N a){A:Family (tent Y H)}{b:Cover}{l:List α}{L U:ℤ}{D d:ℕ}
local notation "payMark"=>distribute Y H v i
open Packing
structure Leased (P:Packing y' j N a) (b:Cover) (d D:ℕ) (A:Family (tent Y H))(L U:ℤ)(l:List α) : Prop extends Packing.Stretch P b d D L U l where
 bill: payMark A=(l.map y').prod
-- field notation okay
lemma Leased.flips (p:Leased Y H v i P' b d D A L U l)(s:ℤ): Leased Y H v i P' b d D (mirror K j (a*s) A) (2*s-U) (2*s-L) (l.map (P'.turn s)):= ⟨p.toStretch.reflection P' s, by rw [(distribute_arith Y H v i A 0 0).2.2.2.2,p.bill,P'.mark_turns]⟩
lemma Leased.forward (p:Leased Y H v i P' b d D A L U l)(s:ℤ): Leased Y H v i P' b d D (relocate K j (a*s) A) (R*s+L) (R*s+U) ((l.map (P'.turn 0)).map (P'.turn (gaugeT K s))) := by
 let q:= (p.flips Y H v i P' 0).flips Y H v i P' (gaugeT K s)
 rw [mul_zero a, show a * gaugeT K s = gaugeT K (a*s) from (by unfold gaugeT Heat.gaugeShift; ring),mul_zero (2:ℤ),zero_sub,zero_sub,sub_neg_eq_add,sub_neg_eq_add, ruler_offset K s] at q
 exact q -- defeq relocate
lemma Leased.combined {B:Family (tent Y H)}{k:List α}{V:ℤ} (p:Leased Y H v i P' b d D A L U l)(q:Leased Y H v i P' b d D B U V k)(x:L≤U)(y:U≤V)(e:V-L≤ (More N).val): Leased Y H v i P' b d D (A*B) L V (l++k):=⟨p.toStretch.tether P' q.toStretch x y e,by rw [(distribute_arith Y H v i A B 0).2.1,p.bill,q.bill,List.map_append,List.prod_append]⟩

-- base atom to long tiled line. 4n copies. fits long banner `R*w*4*n ≤ full period` at root resolution.
variable (w:ℕ){x:α} (p:Leased Y H v i P' b d D A 0 (ruler Λ.block*w) [x])
include p
private lemma toward_lease (n:ℕ):∃ L:List α, Leased Y H v i P' b d D (toward K j (a*w) A n) 0 (R*w) L ∧ L.length=1:=by
 induction n with
 | zero=>exact ⟨[x],p, by simp⟩
 | succ n ih=>
    obtain ⟨u,h,q⟩:=ih; have ht:=h.flips Y H v i P' (gaugeT K w)
    rw [show a*gaugeT K w= gaugeT K (a*w) from by unfold gaugeT Heat.gaugeShift; ring,show 2*gaugeT K w=R*w from ruler_offset K _, sub_self,sub_zero] at ht
    exact ⟨_,ht,by rw [List.length_map,q]⟩
private lemma leases_lace (n:ℕ)(u:R*w*n ≤ (More N).val):∃ L:List α, Leased Y H v i P' b d D (lace K j (a*w) A 1 n) 0 (R*w*n) L ∧ L.length=n:=by
 let t:ℤ:=R*w; have hv:0≤t:= mul_nonneg (ruler_gene _|>.le) (Nat.cast_nonneg _)
 induction n with
 | zero=> exact ⟨[],⟨⟨by simp,by simp,by simp,by simp⟩,by rw [pin_zero,List.map_nil,List.prod_nil]; exact (distribute_arith Y H v i A A 0).2.2.2.1⟩,rfl⟩
 | succ n ih=>
    have hx: t*n ≤ (More N).val:=by change t*(↑(n+1):ℤ) ≤ _ at u; rw [Nat.cast_add_one,mul_add] at u; linarith
    obtain ⟨k₁,p₁,l₁⟩:=toward_lease Y H v i P' w p n
    obtain ⟨k₂,p₂,l₂⟩:= ih hx; have he:= p₂.forward Y H v i P' w; rw [add_zero] at he
    let q:=p₁.combined Y H v i P' he hv (le_add_of_nonneg_right (show 0≤ t*(n:ℤ) by positivity)) (by rw [show R*w+(R*w*n)=R*w*↑(n+1) from by push_cast; ring, sub_zero]; exact u)
    rw [show R*w*↑(n+1)= R*w+(R*w*n) from by push_cast; ring]; refine ⟨_,q,?_⟩; rw [List.length_append,List.length_map,List.length_map,l₂,l₁]; omega
local notation "Y0" z:max n:max=> (R*(w:ℤ)*z-R*w*n)
lemma leases_chambers (n:ℕ)(u:2*(R*w*n) ≤ (More N).val)(z:ℤ) : ∃ l: List α, Leased Y H v i P' b d D (chambers j (a*w) ((a*w)*z) A 1 n) (R*w*z-R*w*n) (R*w*z+R*w*n) l ∧ l.length=2*n:=by
 have he:0≤ R*w*n:=by have h:= ruler_gene Λ.block; positivity
 obtain ⟨k,h,g⟩:= leases_lace Y H v i P' w p n (by omega)
 have hx:= h.flips Y H v i P' 0; rw [mul_zero a,mul_zero (2:ℤ),zero_sub,sub_zero] at hx -- gives (-R*w*n),0
 have hy:= (hx.combined Y H v i P' h (neg_nonpos.mpr he) he (by linarith)).forward Y H v i P' (w*z)
 rw [←mul_assoc,←mul_assoc R,←sub_eq_add_neg] at hy; exact ⟨_,hy,by simp [g,two_mul]⟩
lemma banner_from_unit (n:ℕ)(u:2*(R*w*n) ≤ (N.val:ℤ))(z:ℤ) : ∃ l: List α, Leased Y H v i P' b d D (banner j (a*w) (a*(w*z)) n A) ((Y0 z n)-2*(R*w*n)) ((Y0 z n)+2*(R*w*n)) l ∧ l.length=4*n:=by
 have he:0≤R*w*n:=by have h:=ruler_gene Λ.block; positivity
 have HN:(More N).val=N.val*2:=rfl
 obtain ⟨u₀,q,t⟩:=leases_chambers Y H v i P' w p n (by omega) z
 let g:ℤ:= Y0 z n; have hh:= q.flips Y H v i P' g
 rw [show R*w*z+R*w*n=g+2*(R*w*n) from by unfold g; ring] at hh q
 rw [show 2*g-(g+2*(R*w*n))=g-2*(R*w*n) from by omega, show 2*g-Y0 z n=g from by unfold g; omega, show a*g=gaugeT K (cliff (a*w) ((a*w)*z) n) from ?_] at hh
 rw [←mul_assoc]; exact ⟨_, hh.combined Y H v i P' q (by change g-2*(R*w*n)≤g; omega) (by change g≤g+2*(R*w*n); omega) (by omega),by simp only [List.length_append,List.length_map,t]; omega⟩
 unfold g cliff gaugeT Heat.gaugeShift ruler; change a*(16* _* w * z -16*_ * w*n)=4* (Λ.block.val:ℤ) * _ ; ring
end plots
/- capacity. Goldilocks argument from `SatinThinRenew.renewed`. No length of time
occupied enters transversal generation count. Price needed at most linear in number
of repetitions; applies including seam occupancy at fractional terminal roll. -/
private lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega

lemma transversal_capacity {W B n:ℕ} (p:0<W)(q:0<B)(u:2*B*n≤N.val)(v:N.val≤4*B*n)(e:W≤N.val) :
  ∃ k:ℕ, let J:=(2^k)^3; 2^k*W≤N.val ∧ J*(4*n) ≤ (More N).val^4 ∧
    (More N).val^4 ≤ J*(4*n)*((4*W)^3*(2*B)):=by
 obtain ⟨k,a,t⟩:=goldilock p e; let M':=(More N).val; have he: M'=N.val*2:= rfl; let R:=2^k
 have hZ:R*(4*W)=2*(2*R*W):=by ring
 have hx:M' ≤ R*(4*W):= (Nat.mul_le_mul_right 2 t).trans_eq (by unfold R; ring)
 have hz:R ≤ M':=(le_trans ((Nat.le_mul_of_pos_right R p).trans a) (by omega))
 have hp:4*n≤M':=by have h:=Nat.le_mul_of_pos_left n q; nlinarith
 refine ⟨k,a,(show R^3*(4*n)≤ M'^4 from (Nat.mul_le_mul (Nat.pow_le_pow_left hz _) hp).trans (le_of_eq (by ring))),?_⟩
 calc M'^4 = M'^3*M':= by ring
      _ ≤ (R*(4*W))^3*((4*n)*(2*B)) := Nat.mul_le_mul (Nat.pow_le_pow_left hx _) (by nlinarith only [he,v])
      _= R^3*(4*n)*((4*W)^3*(2*B)) := by ring

end YM.CF.Buffered.Afterglow.Tower.SlabMark.ClockBooking
open YM.CF.Buffered.Afterglow.Tower.SlabMark.ClockBooking
#print axioms banner_from_unit
#print axioms transversal_capacity
