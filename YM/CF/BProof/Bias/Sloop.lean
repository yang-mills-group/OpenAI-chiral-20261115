import YM.CF.BProof.Bias.Slump
/-! C(H) field and D-loss at node roots. Follow dressed hom comparator, never the boot history. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (A B:Stamp){r c:ℝ}{N:Side}{j:ℕ}{R J X:Finset (Per N)}(C:Quilt N)
-- patch all Mark nodes
abbrev Call (R J:Finset (Per N))(A B:Stamp)(C:Quilt N):Prop:=∀ i∈ rowsX R, C (node i) =if i 0∈J then A else B
abbrev Plus (j:ℕ)(M:Male)(R:Finset (Per N))(C:Quilt N) := offCut (Polar j M R) (pair C)
variable {A B C}(b:Call R J A B C)
include b
lemma styleL : Seat R*(pair C-drum N B)=Seat R * (Seat J * drum N (A-B)):= by
 ext i j; rw [timeL,timeL]; split; swap; rfl; rename_i t; rw [timeL,Matrix.sub_apply,drum,drum,pair_local,pair_local,pair_local]; split_ifs with H f -- tune
 · rw [b i.1.1 (row_at.mpr t),if_pos f]; simp [mul_sub]
 · rw [b i.1.1 (row_at.mpr t),if_neg f]; simp
 all_goals simp
lemma styleR: (pair C-drum N B)*Seat R= (Seat J*drum N (A-B))*Seat R := by
 rw [← ((pair_seat R C).sub_right (pair_seat R _)).eq,styleL b, show Commute (Seat R) _ from ((show Commute (Seat R) (Seat J) from time_cut ht R _).mul_right (pair_seat R (fun _=> A-B))) |> Commute.eq] -- tune
-- alternative last expression
variable (M:Male) (h:1≤j)(s:Free c j M R)
omit b
lemma entryBoth(P:Free c j M R): Seat R*Polar j M R=Polar j M R ∧ Polar j M R*Seat R= Polar j M R:=by
 let H: Board ..:= P; rw [seat_eq]; refine ⟨H.holdsPiH,?_⟩; let A:=Polar j M R; have ht:=congrArg star H.holdsPiH; rwa [star_mul,H.wall.isSelfAdjoint,H.PiHp.isSelfAdjoint] at ht
include h s
lemma freeDrum(D:Stamp): Align.Twig (drum N D) (Polar j M R):= by
 let A:= PP R; let B:= QQ R; let F:= Polar j M R; let P:=redP j M N; let U:= drum N D; have ht:=pairBy (rowsX Rᶜ) (fun _=>D) true; exact (entersH (P:=A) (A:=P) (C:=U) s (freeAnti j h M D) ht (pairBy (rowsX Rᶜ) (fun _=>D) false) 0 (by simp)).sub ht
include b
lemma opening : Polar j M R * pair C - pair C * cc (Polar j M R)= commP j M R J * drum N (A-B):=by
 let V:=Polar j M R; let Z:=pair C; let t:= Seat R; let T:=Seat J; let D:= drum N B; let U:=drum N (A-B); have ht: V*(Z-D)=V*(T*U):=by
    rw [←show V*t=V from (entryBoth M s).2,mul_assoc, styleL b,mul_assoc]
 have hu: (Z-D)*cc V=(T*U)*cc V:=by
    have hy : t*cc V=cc V:=by nth_rw 1 [← show cc t=t from timeR_cut ..]; rw [← cc_mul,(entryBoth M s).1]; -- tune
    rw [← hy,←mul_assoc, styleR b, mul_assoc,hy] -- tune
 have hv(V Z D V' :Op (Single N))(h:V*D=D*V') : V*Z-Z*V'=V*(Z-D)-(Z-D)*V':=by rw [mul_sub,sub_mul,h]; abel
 change V*Z-Z*cc V=(V*T-T*V)*U; rw [hv _ _ D _ (freeDrum M h s B),ht,hu,sub_mul, mul_assoc T U, (freeDrum M h s (A-B)).symm, mul_assoc,mul_assoc]
lemma Why(v:(pair C)ᵀ= -pair C) : Polar j M R * pair C-pair C*cc (Polar j M R)= Plus j M R C+(Plus j M R C)ᵀ:=by
 let S:=pair C; let P:=Polar j M R; have he: Pᵀ = cc P:=by unfold cc; rw [show star P=P from (show Board .. from s).PiHp.isSelfAdjoint]
 have ht:(cc P)ᵀ=P:=by rw [←he,Matrix.transpose_transpose]
 change P*S-S*cc P=P*S*(1-cc P)+ (P*S*(1-cc P))ᵀ; -- careful he rewriting P bad
 rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_sub,ht,Matrix.transpose_one,v,he]; noncomm_ring
-- norm estimate for comm on local time slab
lemma plusNorm {r:ℝ} (U:Finset (Per N))(a: ℝ)(α:0≤a)(v:(pair C)ᵀ= -pair C)(e:‖Plus j M R C * Seat U‖≤r)(f:‖Seat U * Plus j M R C‖≤ r)(s':∀ {P:Op (Single N)}, (∀ U:Stamp, Commute (curtain N U) P)→ ‖P‖≤ a* ‖P*drum N (A-B)‖): ‖commP j M R J * Seat U‖≤ a*(r+r):= by
 let P:=Polar j M R; let D:=drum N (A-B); let T:=Seat U; let W:= commP j M R J; let X:=Plus j M R C; have hp(i:Stamp):Commute (curtain N i) P:=by apply commEntry s _ (curtain_p i _ true) (curtain_p i _ false); rw [redP_eq M h]; exact curtain_relic .. -- tune
 apply (s' (fun U'=> (show Commute (curtain N U') (W*T) from (((hp U').mul_right (curtain_seat U' J)).sub_right ((curtain_seat U' J).mul_right (hp U'))).mul_right (curtain_seat U' U)))).trans; apply mul_le_mul_of_nonneg_left _ α; rw [show W*T*D=(X+Xᵀ)*T from (by rw [mul_assoc, (pair_seat ..).eq,←mul_assoc,←opening b M h s,Why b M h s v]),add_mul]; apply (norm_add_le ..).trans; refine add_le_add e ?_
 have hX:Xᵀ*T =cc (star (T*X)):=by unfold cc; rw [star_star, Matrix.transpose_mul,show Tᵀ=T from (by unfold T Seat timeR cutM; simp)] -- tune
 rw [hX, Scroll.norm_cc,norm_star]; exact f
end YM.CF.BProof.Bias
