import YM.SU5.FiniteGaugeData.Nine.FarmerP
set_option autoImplicit false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Pivot
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N:Side}(o:Cover)
open Brique Mir Phase RP Largo Spire
local notation "Μ"=> Single N
open Fock.Brique
variable (k:ℕ)(M:Male)(g:SU.Slot) {h w:ℕ}{P S T: Finset (Single N)} {R:Support (More N)}{D':Finset (Site N)}
local notation "F"=> funde k M N 1
local notation "D"=> Θ N (3:SpinIdx) g
local notation "Η"=> cutM (D)
local notation "W"=> preF k M N g
local notation "L"=> (toolP k M N)
section pom
-- neighbor estimates.Filter cut.Q; no exponential tune just w applied twice.Polar orientation no footprint changes (inherited spin transform)
variable {A B X Y: Op (Single N)}
lemma neigh_mul (p: Neighbor w A)(t:Neighbor h B): Neighbor (w+h) (A*B) := by
 apply neighbor_entry; intro i j v
 rw [Matrix.mul_apply]; refine sum_eq_zero fun u p'=>?_ ; apply mul_eq_zero.mpr; let h':= separation_triangle (node i.1.1) (node u.1.1) (node j.1.1); by_cases t':w<separation (node i.1.1) (node u.1.1); exact Or.inl (neighbor_iff p i u t'); exact Or.inr (neighbor_iff t u j (by omega))
lemma neighProj (S:Finset (Single N)): Neighbor 0 (cutM S):=neighbor_entry (fun i j t=> Matrix.diagonal_apply_ne _ (show i≠j from fun w=>by subst i; simp at t))
lemma neighOne (w:ℕ): Neighbor w (1:Op Μ) := neighbor_entry (fun i j t=> Matrix.one_apply_ne (fun e=> by subst i; simp at t))
lemma neighSub (p:Neighbor w A) (t:Neighbor w B): Neighbor w (A-B):=neighbor_entry (fun i j t'=> by rw [Matrix.sub_apply, neighbor_iff p i j t', neighbor_iff t i j t',sub_self])
lemma neighSpin (A: UNI SpinIdx): Neighbor (N:=N) 0 (prepU (incX 1) A inert N).val:=by
 apply neighbor_entry; rintro ⟨⟨x,i⟩,j⟩ ⟨⟨y,u⟩,p⟩ v; change 0< separation (node x) (node y) at v
 have h:x≠y:=fun e=> by subst x; simp at v
 change jump (Tofu (incX 1) N) (fun i=> (milU (incX 1) A inert i).val) (x,(i,j)) (y,(u,p))=_; rw [jump_apply]; apply if_neg; rw [show Tofu (incX 1) N x=x from ?_]; exact h
 change (lagX 0).mills N x=x; rw [lag_i,map_zero,add_zero]
lemma neighTurn (p:Neighbor w X): Neighbor w (twist (prepU (incX 1) ChiT inert N) X):=by
 let V:= prepU (incX 1) ChiT inert N; have he:Neighbor 0 V.val:= neighSpin ChiT; rw [twist_formula]; exact (zero_add w ▸ Nat.add_zero (0+w) ▸ neigh_mul (neigh_mul he p) (Neighbor.adj he)) -- Nat show equality
variable {c C d:ℝ}
abbrev Liquid (w:ℕ) (X:Op (Single N))(c:ℝ): Prop:= ∃ A:Op (Single N),Neighbor w A∧ ‖A-X‖ ≤ c
lemma liq_turn (p:Liquid w X c): Liquid w (twist (prepU (incX 1) ChiT inert N) X) c:= by obtain ⟨A,h,t⟩:=p; exact ⟨_,neighTurn h,(by rw [←map_sub,twist_norm]; exact t)⟩
lemma liq_inv (p:Liquid w X c):Liquid w (1-X) c := by obtain ⟨A,h,t⟩:=p; exact ⟨_,neighSub (neighOne w) h,(by rw [show 1-A-(1-X)=X-A from (by abel),norm_sub_rev]; exact t)⟩
lemma liq_plus (S:Finset (Single N))(p:Liquid w X c):Liquid w (cutM S*X) c:=by obtain ⟨A,h,t⟩:=p; exact ⟨_,(by simpa using neigh_mul (neighProj S) h),(by rw [←mul_sub]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _)).trans t))⟩
abbrev opt (c:ℝ):= (2+c)*c
lemma opt_pos (c:ℝ)(e:0 ≤ c): 0≤ opt c:=by unfold opt; positivity
lemma approx (u:‖A-X‖≤c)(t:‖B-Y‖≤ c)(x: ‖X‖ ≤1)(y:‖Y‖ ≤1) : ‖A*B-X*Y‖≤opt c:=by
 have he:‖A‖≤1+c:=by linarith only [(norm_sub_norm_le ..).trans u,x]
 rw [show A*B-X*Y=A*(B-Y)+(A-X)*Y from by rw [mul_sub,sub_mul]; abel]; refine (norm_add_le ..).trans ?_; have hv:= (norm_mul_le ..).trans (mul_le_mul he t (norm_nonneg _) ((norm_nonneg A).trans he)); have hx:= (norm_mul_le (A-X) Y).trans ((mul_le_of_le_one_right (norm_nonneg (A-X)) y).trans u); unfold opt; linarith
lemma liq_double (p:Liquid w X c)(t:Liquid w Y c)(x:‖X‖ ≤1)(y:‖Y‖ ≤1)(S:Finset (Single N)): Liquid (2*w) (X*cutM S*Y) (opt c):=by
 rw [mul_assoc,two_mul]; obtain ⟨A,h,v⟩:= p; obtain ⟨B,t,u⟩:= liq_plus S t; have he: ‖cutM S*Y‖ ≤1:=(norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _)).trans y)
 exact ⟨A*B,neigh_mul h t,approx v u x he⟩
-- left & right of σ.X0.
local notation "J"=> piQu o N (toolP k M N)
lemma ort_Flights (p:Liquid w (funde k M N 1) c)(h:1≤k)(t:Aptitude k N): Liquid (2*w) (W) (opt c) ∧ Liquid (2*w) ((piQu o N (toolP k M N))*cutM D*(toolP k M N)) (opt c):=by
 let u:= (L); let he:= liq_inv p; have hx:‖L‖ ≤1:= (tool_proj k M h).norm_le _
 refine ⟨liq_double (X:=L) (Y:=L) he he hx hx _,liq_double (X:=J) ?_ he ((twist_norm ..).le.trans hx) hx _⟩; rw [show J=_ from parity_edge o k M t]; exact liq_turn p
lemma liq_rT (u:Liquid w X c) : Liquid w (X*cutM S) c:=by
 obtain ⟨A,p,q⟩:=u; exact ⟨_,(by simpa using neigh_mul p (neighProj S)), by rw [← sub_mul]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans q)⟩
lemma liq_leak (p:Liquid w X c){U:Support (More N)}(t:Lattice.halo w U⊆ R)(z:S⊆modesIn N U): ‖cutM (modesIn N R)ᶜ*X*cutM S‖ ≤ c:=by
 obtain ⟨A,h,e⟩:=p; let B:= cutM (modesIn N R); let V:=cutM (modesIn N U); let D₀:=cutM S; have he: B*(A*V)=A*V:= by
    have he1:V*star A* B= V*star A:= Neighbor.adj h _ _ t -- tune `h.adj`
    have hB:=congrArg star he1; rwa [star_mul,star_mul,star_star,(show star V= V from (cutM_idp _).2.star_eq),(show star B=B from (cutM_idp _).2.star_eq)] at hB -- count twice
 have hf: B*A*D₀=A*D₀:=by nth_rw 1 2 [← (show V*D₀=D₀ from by unfold V D₀; rw [cut_meet,inter_eq_right.mpr z])]; rw [←mul_assoc _ V _,mul_assoc B A,he, ←mul_assoc A V D₀]
 let C₀:= cutM (modesIn N R)ᶜ; have hx:C₀ * A*D₀=0:=by rw [show C₀=1-B from dim_cut _,sub_mul,sub_mul,one_mul,hf,sub_self] -- line wrong remove
 change ‖C₀*X*D₀‖≤ c; rw [←sub_zero (C₀*X*D₀), ←hx,←sub_mul,←mul_sub]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _)).trans (by rw [norm_sub_rev]; exact e)))) -- tune cutM defeq
end pom
#print axioms liq_leak
end YM.CF.Window.Pivot
