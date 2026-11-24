import YM.CF.Moire.Niche
import YM.SU5.FiniteGaugeData.Signal.ChamberProof
import YM.CF.Vale.Basil
import YM.CF.Buffered.Reflection
/-!
# Local uniformity needed for the finite spanning insertions. This expense is calibrated with
Width purchased on GivenX.Aim etc. (Grace) NOT just assumed on all GramM. Use on actual
histories. Also keep free projector & Tilt data, radius in native units. We use the existing
height grant for Π, Aim, but radii are chosen INDEPENDENT of furnace H (can take H huge later). -/
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Signal
open Function Filter Metric NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Graph Girt Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Kronecker Classical
attribute [local instance] opCStarAlgebra
open Skye RG Laic Nacre Font Pec Thera Branch
open Moire Furnace
namespace Supplies
variable {C a u v r s e:ℝ}{i j b d:ℕ}{n:Side}
/-- `foil` exponent and Goal limit budgets are fixed before h. -/
structure Produce (V:ℕ)(u v b d e:ℝ):Prop where
  outset : ∃ a r:ℝ,∃ k:ℕ,0<a∧0<r∧(∀ m:Side,k≤ m.val→∀ i:Male, Solo a r (funde V i m) e)∧∀ m:Side,k≤ m.val→∀ P:Aim m,P.toll u v b d→ Solo a r (Moire.bloom P) e

lemma gardening (V:ℕ)(P:1≤V){b d u v:ℝ}(p:0<u)(q:0<v)(h:0<b)(hc:0<d):∃ e:ℝ,0<e∧ Produce V u v b d e:=by
 let K:=fun N:Side=> {P:Aim N // P.toll u v b d}; let y(N:Side): K N:=⟨⟨0,0⟩,Vale.empty_pay h.le,Vale.empty_pay hc.le⟩; let A:Type:= ∀ N:Side,K N
 let C:= Male×A
 let f:Tulip.WG C:=fun z N=> funde V z.1 N; let g(z:C)(N:Side):= (z.2 N).val
 have hF:Lively f:=by obtain ⟨s,r,v₁,a,b,h,k,w⟩:=funde_s V P; exact ⟨s,r,v₁,a,b,h,k,fun i N l=>w i.1 N l⟩
 have hG:=terrace g (a:=u) (b:=v) h.le hc.le p q (fun i n=>(i.2 n).property); obtain ⟨a0,r,e,p,q,s,n,t,w⟩:= hF.link hG
 refine ⟨e,s,a0,r,n,p,q,fun m x i=>t (i,y) m x,fun m x F v=>?_⟩; let z:C:=(Vale.babyM,Function.update y m (⟨F,v⟩:K m)); have he:= w z m x; change Solo a0 r (bloom (g z m)) e at he; rwa [show g z m=F by simp [g,z]] at he

lemma Produce.supplement (A:Produce j u v a C e){x:ℝ}(p:0<x)(q:x≤e): Produce j u v a C x:=by
 obtain ⟨r,b,k,v,h,t,w⟩:=A.outset; exact ⟨r,b,k,v,h,fun m p' i=>axis_down _ _ (t m p' i) _ p q,fun m x F v=> axis_down _ _ (w m x F v) _ p q⟩

-- product using same aperture; treat region/observable needs separately
def priceOp {n:Side}(j:ℕ)(P:Aim n)(A:Male)(H:ℝ)(x:Chin n): Op (Single n):= let f:=funde j A n x; upstairs f H * (1-Kennel.capT f (Moire.bloom P x))
lemma atPose {x:Bkg (More n)} (P:Aim n)(A:Male)(H:ℝ): priceOp j P A H (profile x)= upstairs (spar j A x) H * (1-Kennel.capT (spar j A x) (P.den x)):=by unfold priceOp; rw [bloom_P]; rfl
lemma atOne (P:Aim n)(A:Male)(H:ℝ): priceOp j P A H 1=upstairs (funde j A n 1) H:=by simp [priceOp,bloom_zero, Kennel.capT]
lemma Produce.showOp (A:Produce j u v a C e)(H:ℝ):∃ s r:ℝ,∃ i:ℕ,0<s∧ 0<r∧ ∀ m:Side,i ≤ m.val→∀ t:Aim m,t.toll u v a C→∀ l:Male, Solo s r (priceOp j t l H) e:=by
 obtain ⟨s,r,k,h,p,hF,hT⟩:=A.outset
 let X:= Real.exp s; let x:= X+r
 let B:= ‖(((H⁻¹:ℝ):ℂ))‖ *r+‖(H:ℂ)‖*x; let D:= (2:ℝ)*(B*(X+(2*(2*(x*r)*r))))
 refine ⟨s,max 1 D,k,h,lt_max_of_lt_left one_pos,fun m i t q l=>?_⟩
 let y:= funde j l m; let S:= Moire.bloom t; have he:= hT m i t q; have ht:= hF m i l; have hh: Solo s X (fun _ : Chin m=>1) e:= Crown.ident ..
 have hfree: Solo s x (fun i=> 1-y i) e:= Crown.sub hh ht
 have HB:Solo s B (fun i=> upstairs (y i) H) e:= Crown.plus (Crown.scale ht (↑(H⁻¹):ℂ)) (Crown.scale hfree (↑H:ℂ))
 have hr: Solo s D (priceOp j t l H) e:= Crown.product HB (Crown.sub hh (Crown.product (Crown.product hfree he h.le) ht h.le)) h.le
 exact Crown.books hr (le_max_right ..)
section localization
variable {k d d':ℕ}
local notation "F"=> forum n e
local notation "l↓" S=> Branch.strip (forum n e) S
variable {D:Type*}{W Y I A:Type*}[TopologicalSpace D] [Fintype Y][DecidableEq Y][Fintype I][DecidableEq I]
open Branch
variable {b:Stage Y I D A} {O:Op I}
-- assorted stencil geometry lemmas tailored to column-mode incidence
lemma locates (h: FiniteOp b k O) (x:Y): Branch.strip b (bay b.F x (d+k))* (O * Branch.strip b (bay b.F x d))= O*Branch.strip b (bay b.F x d):=by
  ext i j; rw [stripL,stripR]; split; rfl
  next v=> split; next w=>
             apply Eq.symm; apply h; have u:= b.F.tri x (b.home j) (b.home i); rw [b.F.sym (b.home j)] at u; have ht:= (bay_mem _).1 w; exact lt_of_not_ge (fun g=> v ((bay_mem _).2 (u.trans (Nat.add_le_add ht g))))
           rfl -- tune
lemma narrow {u v:Seal Y}(p:u ⊆ v): Branch.strip b v * Branch.strip b u= Branch.strip b u:=by
 ext i j; rw [stripL]; split; rfl
 next h=>
            rw [Branch.strip,cutM]; by_cases z:i=j; · subst j; simp [board,(mt (fun g=> p g) h)] -- mt parse
            simp [z]

-- cage and column price (can pay δ independent of length when columns used)
def Focus {b:Stage Y I D A} (o:Y) (k d:ℕ)(v:Ket I):Prop:= acts (Branch.strip b (bay b.F o d)) v=v -- remove k
lemma deep(o:Y){x k:ℕ}(p:d≤x){v:Ket I}(e:Focus (b:=b) o k d v): acts (Branch.strip b (bay b.F o x)) v=v:=by
 nth_rw 1 [←(show acts _ _ = _ from e)]; rw [←act_mul,narrow (v:=bay b.F o x) (b:=b) (fun i z=> (bay_mem _).mpr (((bay_mem _).1 z).trans p)),e]
lemma locked(o:Y){v:Ket I}(h:FiniteOp b k O)(p:d+k ≤ d')(e:acts (Branch.strip b (bay b.F o d)) v=v): acts (cage b o d' O) v=acts O v:=by
 rw [cage,act_mul,(deep o (by omega:d≤d') (k:=0) e),act_mul]; let x:= Branch.strip b (bay b.F o d); have he: O*x=Branch.strip b (bay b.F o (d+k))* (O*x):=Eq.symm (locates h o); nth_rw 1 [←e]; rw [←act_mul,←act_mul,mul_assoc,he,←mul_assoc (Branch.strip b (bay b.F o d')), narrow (b:=b) (u:=bay b.F o (d+k)) (v:=bay b.F o d') (fun i z=> (bay_mem _).2 (((bay_mem _).1 z).trans p)),←he,act_mul,e]

-- deployment prizes on actual account. cost threshold does not depend on observing k twice.
variable {f: Raw D I}{X Z:Tag b}{m:ℕ}{r:ℝ}
lemma sunray (a r:ℝ)(h:0<a)(g:0<r)(s:ℝ)(p:0<s):∃ l:ℕ,Real.exp (-a/2*(l:ℝ))*r≤ s:=by
 let W:=Real.log (r/s); obtain ⟨l,k⟩:= exists_nat_ge ((2/a)*W); refine ⟨l,?_⟩
 field_simp at k
 rw [←le_div_iff₀ g, ←Real.exp_log (div_pos p g)]
 apply Real.exp_monotone; unfold W at k; rw [Real.log_div p.ne' g.ne']; rw [Real.log_div g.ne' p.ne'] at k; linarith

lemma auxQ (V:Op I)(v:Ket I) : ‖acts V v‖ ≤ ‖V‖*‖v‖:= by apply ((acts V).le_opNorm v).trans; rw [show ‖acts V‖=‖V‖ from Matrix.l2_opNorm_toEuclideanCLM V]
lemma supply (V:RootedK X Z a r f) (p:0<a) (z:ℝ)(t:0<z)(l:ℕ)(e: Real.exp (-a/2*(l:ℝ))*r≤z):∃ g:Raw D I,(∀ d, FiniteOp b l (g d)) ∧ (∀ d, ‖f d-g d‖≤z)∧ ∀ x y o v k, acts (Branch.strip b (bay b.F o k)) v=v→ ‖acts (g x-g y) v‖ ≤ r*b.eval (bay b.F o (k+l+l)) x y*‖v‖:=by
 obtain ⟨N,C,q,h,H⟩:=V
 let G:= lop N l; refine ⟨G,fun d=>lop_rad N C q d,fun d=> ((lip_tail N C q h H p.le).boundOp (half_pos p).le d).trans e,fun x y o v k v'=>?_⟩
 let W' := cage b o (k+l); have hh(d:D): acts (W' (G d)) v=acts (G d) v:= locked o (lop_rad N C q d) le_rfl v'
 rw [act_sub,←hh, ←hh, ←act_sub]; exact (auxQ _ _).trans (mul_le_mul_of_nonneg_right (cage_lip N C q h p.le o x y (k+l) l) (norm_nonneg _)) -- need LinearOrder on I; better custom
end localization
end Supplies
end YM.CF.Signal
