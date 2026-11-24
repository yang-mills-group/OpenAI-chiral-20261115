import YM.CF.Moire.Niche
import YM.CF.Proa.Yard
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{u v:Bool}{L:Side}{F:WG ι}
lemma ThinSlope (A:Script ι)(k: Save L u u @A)(h:∀ i {N P:Side}(G:Ratio N P),G.count=L→ A i G 1=0)(r:ℝ)(hr:0<r):Slope L @A r:=by
 obtain ⟨a,c,e,p,w,l,v,W⟩:=k; obtain ⟨b,m,w',l,-,t,Y⟩:= curve W p w l r hr (fun i N P G f _=>h i G f); exact ⟨m,l,t,fun i _ _ G hg hp x g=> (Y i G hg hp).lib.boundOp w'.le ⟨x,g⟩⟩
lemma graphite (A:Script ι)(k:Save L u u @A)(h:∀ i {N P:Side}(G:Ratio N P),G.count=L→A i G 1=0) : Save L u u (fun i _ _ G x=> pencil (A i G x)):=by
 obtain ⟨e,l,v,H⟩:= ThinSlope @A k @h (1/2) (by norm_num)
 obtain ⟨b,c,M,δ,hb,hc,hr,hM,hδ,K,W⟩:= Peaks.series u k (show 0<(1:ℝ)/2 by norm_num) (by norm_num) l H
 let V(z:ℕ):= M*c^(z+1); have hp: Summable V:=by unfold V; simp_rw [pow_succ, ← mul_assoc]; exact ((summable_geometric_of_lt_one hc.le hr).mul_left _).mul_right _
 refine recorded (k:=K) (fun i N P G he ht=>Crown.tsK V (fun n=>?_) hb.le hp) hb hδ
 let Y:= (W (n+1) i G he ht).scale ((bcoef n):ℂ); apply ((Y.books (show _ ≤ V n from mul_le_of_le_one_left (by positivity) (by simpa using bc_norm n)))) -- real smul
 -- tune
lemma transportS {K:Script ι}(h:Save L u v @K){S:Type*}(g:S→ι): Save L u v (fun i _ _ G x=> K (g i) G x):=by obtain ⟨p,c,e,h,l,w,r,H⟩:=h; exact recorded (k:=r) (fun i _ _ G j k=> H (g i) G j k) h w
open Kennel
variable (L) (ho: Odd L.val)(j:ℕ) (hj:Even j)(hu:1≤j) (K:WG ι)(H:Lively K)(p:∀ i n,K i n 1=0)(S:ι→Male)
abbrev prime : Script ι:= fun i _ _ G x=>capT (foal j true (S i) G x) (foot G (K i _ x.1))
abbrev nuke : Script ι:= fun i _ _ G x=> bentT (pine j L ho (Thread j) true (S i) G x) (wh j L ho true (S i) G x) (ticketT (Thread j) true (S i) G x) (prime j K S i G x)
abbrev prism : Script ι:= fun i _ _ G x=>traitP (wh j L ho true (S i) G x) (pine j L ho (Thread j) true (S i) G x) (ticketT (Thread j) true (S i) G x) (prime j K S i G x)
include p in
lemma pale_z (i:ι){N P:Side}(G:Ratio N P): prime j K S i G 1=0:=by unfold prime capT; rw [show foot G (K i P _) =0 from ?_,mul_zero,zero_mul]; rw [show ((1:Coil N P).1)=(1:Chin P) from rfl,p]; rfl
include p in
lemma nuke_z(i:ι){N P:Side}(G:Ratio N P):nuke L ho j K S i G 1=0:=by rw [nuke,bentT, pale_z _ _ p,mul_zero]
include p in
lemma pris_z (i:ι){N P:Side}(G:Ratio N P): prism L ho j K S i G 1=laneP (wh j L ho true (S i) G 1) (ticketT (Thread j) true (S i) G 1) (pine j L ho (Thread j) true (S i) G 1):=by unfold prism traitP laneP; rw [pale_z j K p, add_zero,mul_one]; simp [creep,bentT]
include hj hu H p
lemma prism_s : Save L true true (prime j K S)∧ Save L true true (nuke L ho j K S) ∧ Save L false false (prism L ho j K S):=by
 obtain ⟨R,h,V⟩:=cup j L ho hj hu (canUse j L ho) true
 let W:=transportS R S; let B:=transportS V S; let X:=transportS h S; let Q:= transportS (pine_funds j L ho hj hu _ (canUse j L ho) true) S
 let Z:Save L true true (prime j K S):=(((Save.one ι).sub X).mul (flowers K H)).mul X
 let A:=nuke L ho j K S; have ht:Save L true true @A:=(Q.mul (B.mul W)).mul Z
 refine ⟨Z,ht,?_⟩
 have hz:Save L true true (fun i _ _ G x=> (1+A i G x)⁻¹):= (righted true true (A:=fun i _ _ G x=> 1+A i G x) (B:=fun _ _ _ _ _=>1) ((Save.one ι).plus ht) (Save.one ι) (fun i N P G h=>by unfold A; rw [nuke_z _ _ _ _ p,add_zero,one_mul])).1
 exact (((Save.one _).sub B).mul (W.mul ((Save.one _).plus Z))).mul (hz.mul Q)
lemma pier_s : Slope L (nuke L ho j K S) (1/2) ∧ Save L true true (fun i _ _ G x=> pencil (nuke L ho j K S i G x)):=by
 have hx:= (prism_s L ho j hj hu K H p S).2.1; exact ⟨ThinSlope _ hx (fun i N P G e=> nuke_z _ _ _ _ p _ i G) _ (by norm_num), graphite _ hx (fun i N P G e=> nuke_z _ _ _ _ p _ i G)⟩
end YM.CF.Proa
