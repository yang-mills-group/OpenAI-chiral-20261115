import YM.SU5.Reconstruction.Cashier.Mural

/-! Saturated reservoir at given regulator. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Pannier.Chancel.Cliplet
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Buffered.Afterglow Buffered.Afterglow.Journey
open Mir Phase RP Reflect Advance Nacre Vale Girt Lifted Scree Tower
open Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m n:Side}{B l: ℕ} {M:Tulip.Male} {j k w d t:ℕ}{γ τ R:ℝ}
namespace Mural
open Tower.SlabMark
private lemma goldibar {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by -- from Trefl, private
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
abbrev gong (K:Calibration) := 16*K.B.val
structure Invoice (K:Calibration) (B u:ℕ):Prop where
 lo:12*B ≤ gong K*u
 top: gong K*u ≤ 2*(12*B+addgap K)
lemma billing (e:addgap K ≤ B): ∃ u:ℕ,0<u ∧ Invoice K B u:=by
 let n:=12*B; let b:= gong K; let u:=n/b+1
 have h₀ : b>0:=Nat.mul_pos (by decide) K.B.property
 have hx:0 < B:= addgap_pos.trans_le e
 have hz:= Nat.mod_add_div n b
 have hB : b ≤ 2*B:= by unfold addgap stepgap at e; unfold b gong; omega
 have hw:= Nat.mod_lt n h₀; refine ⟨u,Nat.succ_pos _,?_⟩
 have h:b*u=b*(n/b)+b:=by unfold u; ring
 refine ⟨show n≤b*u from by omega,show b*u≤2*(n+addgap K) from by unfold n at *; omega⟩
variable {F:Buffered.Family K} {u:ℕ}
private lemma elongated {ν:Mark (K.c m)→ℂ}(h:StageTw K ν j R d M) (q:addgap K≤ B) (hu:0<u) (c:Invoice K B u) (i:Axis) {l:ℕ}
  (e:2*gong K*u*l ≤ (K.c m).val) (a:(K.c m).val ≤ 4*gong K*u*l)
  (b:12*B+addgap K≤(K.c m).val)(A:Cliplet (K.c m) k)(p:Perron j M w d t γ τ A)
  (Z:A.broad=Islet (K.c m) (grain B) B)(y:F m=A.frame)(s:ℤ):
  ∃ r:ℕ,∃ L:List (Cliplet (K.c m) k), Flight j M w d t γ τ L ∧ 0<r∧L.length= 4*l*r∧ L.length ≤ (More (K.c m)).val^4∧
       (More (K.c m)).val^4 ≤ L.length*(4*(12*B+addgap K))^4 ∧ ‖ν ((SlabMark.banner i u s l F) m)‖^r≤ ‖ν (probe L)‖ ∧ ∃ W:List (Cliplet (K.c m) k), Flight j M w d t γ τ W ∧ W.length=4*l ∧ (SlabMark.banner i u s l F) m=probe W:=by
 let Z₁:=Sen (grain B) B; let n:=K.c m
 have hB:=addgap_pos.trans_le q; have hg:0<n.val:=n.property; have hk:12*B+addgap K>0:=by omega
 have hp:Between K i 0 (ruler K.B*u) Z₁:= between_grain q i _ (by
    unfold ruler; have h:=c.lo; unfold gong at h; exact_mod_cast h)
 have ht:Transom i Z₁ (fun _=>0) (12*B):=by
   intro i _ x r; have h:=bounds_Sen_grain r i; dsimp; omega
 have hc:Cargo K m j k w d t γ τ M i 0 (ruler K.B*u) (fun _=>0) (12*B) 1 F:=⟨[A],Flight.alone p,(by simp [y]),rfl,Z₁,hp,ht,(by rw [show whereV [A]=A.broad by simp [whereV],Z,sen_islet])⟩
 have hv:=banners h i hc (by exact_mod_cast hu.le) l (by unfold ruler; unfold gong at e; rw [show 2*((16:ℤ)*↑K.B.val*↑u*↑l)=2*(16:ℤ)*↑K.B.val*↑u*↑l by ring]; rw [mul_assoc 2 (16:ℤ) (↑K.B.val:ℤ)]; exact_mod_cast e) s
 obtain ⟨X,v,pV,r,A,hA,hX,px⟩:= hv
 obtain ⟨k',a',l'⟩:= goldibar hk b
 let d':=univ.erase i
 have hm(k:Axis)(x:k∈ d') : cows k (whereV X) (12*B):=by
   refine ⟨0,fun y v=>?_⟩
   obtain ⟨t,w,rfl⟩:=mem_image.mp (px v); exact ⟨t k,(hX _ (mem_erase.mp x).1 _ w).1,(hX _ (mem_erase.mp x).1 _ w).2,rfl⟩
 obtain ⟨L,f,T,vv⟩:=h.scatter rfl a' d' X v hm
 have e':d'.card=3:=by simp [d',card_erase_of_mem,Axis]
 let q':ℕ:=2^k'; let R':= 12*B+addgap K; have wt:L.length=4*l*q'^3:=by rw [T,e',r]; unfold q'; ring
 have hu':0 < gong K*u:=mul_pos (Nat.mul_pos (by decide) K.B.property) hu
 refine ⟨q'^3,L,f,by unfold q'; positivity,wt,?_,?_,by rw [e'] at vv; rw [pV]; exact vv,(⟨X,v,r,pV⟩)⟩
 · change _ ≤ (n.val*2)^4; rw [wt, show (n.val*2)^4=(n.val*2:ℕ)*(n.val*2)^3 by ring]
   have he':2*(gong K*u)*l ≤ n.val:=by rw [← mul_assoc] ; exact e
   refine mul_le_mul' ?_ ?_
   · refine le_trans (b:=2*(2*(gong K*u)*l)) (by nlinarith) (by linarith)
   apply pow_le_pow_left'; exact le_trans (a'.trans' (Nat.le_mul_of_pos_right q' hk)) (by unfold n; omega) -- sideways
 change (n.val*2)^4 ≤ _; rw [wt]; change _ ≤ _ *(4*R')^4
 calc _ = (n.val*2) * (n.val*2)^3:= by ring
      _ ≤ (4*l*(4*R')) * (q'*(4*R'))^3 := by
         have ht:gong K*u ≤2*R':=c.top
         have he:(n.val*2) ≤4*l*(4*R'):= (Nat.mul_le_mul_right 2 a).trans (by nlinarith)
         have hl:(n.val*2) ≤ q'*(4*R'):= (Nat.mul_le_mul_right 2 l').trans (le_of_eq (by unfold q' R'; ring))
         gcongr
      _ = _:= by ring
open Tapestry
lemma cellar {ν:Mark n→ℂ}(x: K.c m=n)(h:StageTw K ν j R d M)(q:addgap K≤ B)(hu:0<u)(c:Invoice K B u)(i:Axis)(l:ℕ)
  (e:2*gong K*u*l ≤ n.val)(a:n.val≤ 4*gong K*u*l)
  (b:12*B+addgap K≤n.val)(A:Cliplet n k)(p:Perron j M w d t γ τ A)
  (Z:A.broad=Islet n (grain B) B)(y: Tapestry.arrange _ n x (F m)=A.frame)(s:ℤ):
  ∃ r:ℕ, ∃ L:List (Cliplet n k), Flight j M w d t γ τ L ∧ 0<r∧L.length=4*l*r∧ L.length ≤ (More n).val^4 ∧
      (More n).val^4 ≤ L.length*(4*(12*B+addgap K))^4 ∧ ‖ν (Tapestry.arrange _ n x ((SlabMark.banner i u s l F) m))‖^r ≤ ‖ν (probe L)‖ ∧ ∃ W:List (Cliplet n k), Flight j M w d t γ τ W ∧ W.length=4*l ∧ Tapestry.arrange _ n x ((SlabMark.banner i u s l F) m)=probe W:= by subst n; exact elongated h q hu c i e a b A p Z y s
end Mural
end YM.CF.Pannier.Chancel.Cliplet
#print axioms YM.CF.Pannier.Chancel.Cliplet.Mural.cellar
