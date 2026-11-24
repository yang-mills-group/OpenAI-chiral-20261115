import YM.CF.BProof.Trek.Zone
import YM.CF.BProof.Tape.Contour
/-! P bits, flux and vacancy grant. Comparison on Stamp and μ. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators Hearth
attribute [local instance] opCStarAlgebra
variable {s c a:Side} (Y:Yard (More s))(D:Script Y){u v d:ℝ}{H:Herald u v}{t:ℕ} (C:Sized t H.whole) (g: Ratio c (More s))(B:Blocks Y c)(F:Bkg (More s))(f:Ratio a (More s))
-- P bits omit faces: not in bands.
def Pins := univ.filter fun x: Site s=>¬ dark Y (node x)∧ distant Y g B (node x) 6
lemma pins (x:Site s) : x∈ Pins Y g B ↔ ¬dark Y (node x)∧ distant Y g B (node x) 6:=by simp only [Pins,mem_filter,mem_univ,true_and]
lemma empty_pins : Pins Y g ∅=univ.filter fun x=>¬dark Y (node x):=by ext x; simp [Pins,distant,emptyB]

-- for any node in gap, march into next Mark in δ. assume l≥2d. no alignment or parity needed beyond standard node maps.
lemma vacancy (h:2*Y.short≤Y.long) : Fig.Shut Y.short 0 (Pins Y g B) := by
 intro x hx; let D:= Y.short; obtain ⟨he,hb⟩:= (pins ..).1 hx; refine ⟨D,le_rfl,fun e=>(pins ..|>.1 e).1 ?_⟩; let s₁:=time (node x); -- s shadow tune
 let i:=tag Y (node x); let a:=along (Y.v i) s₁; have ht:a≤D:=mem_strip.mp (gap_pick Y (node x) he); let z:= x+D • step 0
 have hv(k:ℕ): time (node (x+k • step 0))=s₁+ (↑(2*k): Per (More s)):=by
    induction k with | zero=>simp [s₁] | succ k ih=> rw [add_smul,one_smul,←add_assoc, Cube.after,time_add,time_add,ih]; push_cast; simp [mul_add]; ring -- group additive mixed zmod
 have hp:=Y.last_edge i; have hh: time (node z)= Y.pole (i+1)+ (↑(a+D):Per (More s)) := by
    rw [show time (node z)=_ from hv D,← Y.last_edge]; change s₁+(↑(2*D): Per _) =Y.v i+(D:Per _)+(↑(a+D):Per (More s)); nth_rw 1 [← add_along (Y.v i) s₁]; push_cast; unfold a; ring -- casts tune
 exact (codeB Y (mem_strip.mpr (show along (Y.pole (i+1)) (time (node z))≤Y.long from (by rw [hh,along_add _ (by have :=Y.lL; unfold D at *; omega)]; unfold D at *; omega)))).1
namespace Permit
variable {Y D C g B F f} {U:Bkg (More s)}{r:ℝ}(L: Pad Y H C g.count.val)(p:Permit D C U g B d)(T:4≤a.val)(W:f.count=H.whole) (e:Lamp C g B r U F)(S:Sound Y H C d)
variable {q k':ℝ}{k:ℕ} (t':k≤t)
include L p T W e S t'
lemma dear(x:Site (More s))(p':x∈ halo k (Hearth.spot (Pins Y g B))): distant Y g B x 3 ∧ Y.Vic (tag Y x) t (time x):=by
 obtain ⟨y,h,u⟩:= halo_spec.mp p'; obtain ⟨y,hk,rfl⟩:= mem_image.mp h; obtain ⟨d,v⟩:= (pins ..).1 hk; obtain ⟨ha,hb,hc,hd,hh⟩:=p.into L _ x (gap_pick Y _ d) v (u.trans t'); exact ⟨hc,hb ▸ hh⟩
lemma halo_pay (u:xm*d≤ q) : Hearth.CloseH F q (Pins Y g B) k := by
 intro x v; obtain ⟨v,p'⟩:= (mem_filter.mp v).2; obtain ⟨hV,hx⟩:= p.dear L T W e S t' x.1 v; have hg:= ((p.ground x (Y.vic_nearer _ t _ _ (by have hp:=C.beginU; omega) hx) (clear_weaker Y g B _ _ hV (by omega))))
 have hp(x:Site (More s))(h:x∈halo k (Hearth.spot (Pins Y g B))):x∈ ChillF Y g B C.blockY :=(p.expand_true L S T W e x (.inr (p.dear L T W e S t' x h).1)).1
 apply (optic _ _).trans; rw [cd_symm, cd_one, ← e.outside x (hp _ v) (hp _ p')]; exact (mul_le_mul_of_nonneg_left hg xm_p.le).trans u
-- prices: per-z P sets choose constant disk.
lemma view1 (u:2*xm*d≤q)(A:HScope s 3)(h:A.val= fun y=>D.HH C g B F f y 1) (w:ℝ): Hearth.Picture s A (Pins Y g B) q k' w k:=by
 constructor; intro z h'; refine ⟨BB,(CStarRing.norm_of_mem_unitary (threesK lv lk).norm).le.trans one_le_two,Or.inl (fun i m=>?_)⟩ -- tune `.flight` nonexistent
 rw [h]; dsimp only; obtain ⟨t,ht⟩:=p.dear L T W e S t' _ (halo_spec.mpr ⟨_,h',(bay_mem _).mp m⟩); exact (p.zero_f L S T W e _ t ht).trans u
omit L p T W e S t' in
lemma innerModel (M:Fin 5→Stamp)(q:ℝ)(e:∀ i,tightLoop M q i)(h:q<1)(i:Fin 5): ‖M i‖≤2:=by
 have ht:=e i 0 z0; rw [Gig_0,norm_sub_rev] at ht; have he:‖BB‖=1:= CStarRing.norm_of_mem_unitary (threesK lv lk).norm; exact le_trans (norm_le_norm_sub_add (M i) BB) (by linarith)
lemma priced (M: Fin 5→Stamp)(v:∀ i,tightLoop M q i)(h:q<1)(u:2*xm*d+q ≤ k')(rₚ w:ℝ)(hv:1≤w)(A:HScope s 3)(u':A.val=fun y=> D.HH C g B F f y w): Hearth.Picture s A (Pins Y g B) rₚ k' 0 k:=by -- q/r A price should any swap
 constructor; intro z z'; refine ⟨M (D.code z),innerModel M q v h (D.code z), Or.inr ⟨rfl,fun j _ l=>?_⟩⟩; obtain ⟨x,h,rfl⟩:= mem_image.mp z'; let G:=tag Y (node x);  -- z erased
 obtain ⟨x₁,x₂⟩:= (pins ..).1 h; obtain ⟨h,hx,g,y,t⟩:= p.into L _ (node j) (gap_pick Y (node x) x₁) x₂ (((bay_mem _).mp l).trans t'); obtain ⟨t₀,v₁,φ,-⟩:=p.vision L S T W e _ g (hx ▸ t) hv; rw [u',y]; exact (((norm_sub_le_norm_sub_add_norm_sub _ (Gig (D.code (node j)) t₀) _).trans (add_le_add φ (v (D.code (node j)) _ v₁))).trans u) -- shadow
end Permit
end YM.CF.BProof.Trek
