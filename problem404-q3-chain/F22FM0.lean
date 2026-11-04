import ExactF22
import F22DataS
import F22DataC
import F22DataD1

set_option exponentiation.threshold 1024
set_option maxHeartbeats 4000000
set_option maxRecDepth 262144
-- flatMap decides.
theorem fz_FM_0 : (fz_S_0.filter (fun st => decide (fz_C_0.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_0.2.1 st.1 st.2 fz_C_0.2.2]) = fz_L_0 := by decide +kernel
theorem fz_FM_1 : (fz_S_1.filter (fun st => decide (fz_C_1.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_1.2.1 st.1 st.2 fz_C_1.2.2]) = fz_L_1 := by decide +kernel
theorem fz_FM_2 : (fz_S_2.filter (fun st => decide (fz_C_2.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_2.2.1 st.1 st.2 fz_C_2.2.2]) = fz_L_2 := by decide +kernel
theorem fz_FM_3 : (fz_S_3.filter (fun st => decide (fz_C_3.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_3.2.1 st.1 st.2 fz_C_3.2.2]) = fz_L_3 := by decide +kernel
theorem fz_FM_4 : (fz_S_4.filter (fun st => decide (fz_C_4.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_4.2.1 st.1 st.2 fz_C_4.2.2]) = fz_L_4 := by decide +kernel
theorem fz_FM_5 : (fz_S_5.filter (fun st => decide (fz_C_5.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_5.2.1 st.1 st.2 fz_C_5.2.2]) = fz_L_5 := by decide +kernel
theorem fz_FM_6 : (fz_S_6.filter (fun st => decide (fz_C_6.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_6.2.1 st.1 st.2 fz_C_6.2.2]) = fz_L_6 := by decide +kernel
theorem fz_FM_7 : (fz_S_7.filter (fun st => decide (fz_C_7.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_7.2.1 st.1 st.2 fz_C_7.2.2]) = fz_L_7 := by decide +kernel
theorem fz_FM_8 : (fz_S_8.filter (fun st => decide (fz_C_8.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_8.2.1 st.1 st.2 fz_C_8.2.2]) = fz_L_8 := by decide +kernel
theorem fz_FM_9 : (fz_S_9.filter (fun st => decide (fz_C_9.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_9.2.1 st.1 st.2 fz_C_9.2.2]) = fz_L_9 := by decide +kernel
theorem fz_FM_10 : (fz_S_10.filter (fun st => decide (fz_C_10.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_10.2.1 st.1 st.2 fz_C_10.2.2]) = fz_L_10 := by decide +kernel
theorem fz_FM_11 : (fz_S_11.filter (fun st => decide (fz_C_11.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_11.2.1 st.1 st.2 fz_C_11.2.2]) = fz_L_11 := by decide +kernel
theorem fz_FM_12 : (fz_S_12.filter (fun st => decide (fz_C_12.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_12.2.1 st.1 st.2 fz_C_12.2.2]) = fz_L_12 := by decide +kernel
theorem fz_FM_13 : (fz_S_13.filter (fun st => decide (fz_C_13.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_13.2.1 st.1 st.2 fz_C_13.2.2]) = fz_L_13 := by decide +kernel
theorem fz_FM_14 : (fz_S_14.filter (fun st => decide (fz_C_14.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_14.2.1 st.1 st.2 fz_C_14.2.2]) = fz_L_14 := by decide +kernel
theorem fz_FM_15 : (fz_S_15.filter (fun st => decide (fz_C_15.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_15.2.1 st.1 st.2 fz_C_15.2.2]) = fz_L_15 := by decide +kernel
theorem fz_FM_16 : (fz_S_16.filter (fun st => decide (fz_C_16.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_16.2.1 st.1 st.2 fz_C_16.2.2]) = fz_L_16 := by decide +kernel
theorem fz_FM_17 : (fz_S_17.filter (fun st => decide (fz_C_17.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_17.2.1 st.1 st.2 fz_C_17.2.2]) = fz_L_17 := by decide +kernel
theorem fz_FM_18 : (fz_S_18.filter (fun st => decide (fz_C_18.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_18.2.1 st.1 st.2 fz_C_18.2.2]) = fz_L_18 := by decide +kernel
theorem fz_FM_19 : (fz_S_19.filter (fun st => decide (fz_C_19.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_19.2.1 st.1 st.2 fz_C_19.2.2]) = fz_L_19 := by decide +kernel
theorem fz_FM_20 : (fz_S_20.filter (fun st => decide (fz_C_20.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_20.2.1 st.1 st.2 fz_C_20.2.2]) = fz_L_20 := by decide +kernel
theorem fz_FM_21 : (fz_S_21.filter (fun st => decide (fz_C_21.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_21.2.1 st.1 st.2 fz_C_21.2.2]) = fz_L_21 := by decide +kernel
theorem fz_FM_22 : (fz_S_22.filter (fun st => decide (fz_C_22.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_22.2.1 st.1 st.2 fz_C_22.2.2]) = fz_L_22 := by decide +kernel
theorem fz_FM_23 : (fz_S_23.filter (fun st => decide (fz_C_23.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_23.2.1 st.1 st.2 fz_C_23.2.2]) = fz_L_23 := by decide +kernel
theorem fz_FM_24 : (fz_S_24.filter (fun st => decide (fz_C_24.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_24.2.1 st.1 st.2 fz_C_24.2.2]) = fz_L_24 := by decide +kernel
theorem fz_FM_25 : (fz_S_25.filter (fun st => decide (fz_C_25.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_25.2.1 st.1 st.2 fz_C_25.2.2]) = fz_L_25 := by decide +kernel
theorem fz_FM_26 : (fz_S_26.filter (fun st => decide (fz_C_26.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_26.2.1 st.1 st.2 fz_C_26.2.2]) = fz_L_26 := by decide +kernel
theorem fz_FM_27 : (fz_S_27.filter (fun st => decide (fz_C_27.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_27.2.1 st.1 st.2 fz_C_27.2.2]) = fz_L_27 := by decide +kernel
theorem fz_FM_28 : (fz_S_28.filter (fun st => decide (fz_C_28.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_28.2.1 st.1 st.2 fz_C_28.2.2]) = fz_L_28 := by decide +kernel
theorem fz_FM_29 : (fz_S_29.filter (fun st => decide (fz_C_29.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_29.2.1 st.1 st.2 fz_C_29.2.2]) = fz_L_29 := by decide +kernel
theorem fz_FM_30 : (fz_S_30.filter (fun st => decide (fz_C_30.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_30.2.1 st.1 st.2 fz_C_30.2.2]) = fz_L_30 := by decide +kernel
theorem fz_FM_31 : (fz_S_31.filter (fun st => decide (fz_C_31.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_31.2.1 st.1 st.2 fz_C_31.2.2]) = fz_L_31 := by decide +kernel
theorem fz_FM_32 : (fz_S_32.filter (fun st => decide (fz_C_32.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_32.2.1 st.1 st.2 fz_C_32.2.2]) = fz_L_32 := by decide +kernel
theorem fz_FM_33 : (fz_S_33.filter (fun st => decide (fz_C_33.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_33.2.1 st.1 st.2 fz_C_33.2.2]) = fz_L_33 := by decide +kernel
theorem fz_FM_34 : (fz_S_34.filter (fun st => decide (fz_C_34.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_34.2.1 st.1 st.2 fz_C_34.2.2]) = fz_L_34 := by decide +kernel
theorem fz_FM_35 : (fz_S_35.filter (fun st => decide (fz_C_35.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_35.2.1 st.1 st.2 fz_C_35.2.2]) = fz_L_35 := by decide +kernel
theorem fz_FM_36 : (fz_S_36.filter (fun st => decide (fz_C_36.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_36.2.1 st.1 st.2 fz_C_36.2.2]) = fz_L_36 := by decide +kernel
theorem fz_FM_37 : (fz_S_37.filter (fun st => decide (fz_C_37.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_37.2.1 st.1 st.2 fz_C_37.2.2]) = fz_L_37 := by decide +kernel
theorem fz_FM_38 : (fz_S_38.filter (fun st => decide (fz_C_38.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_38.2.1 st.1 st.2 fz_C_38.2.2]) = fz_L_38 := by decide +kernel
theorem fz_FM_39 : (fz_S_39.filter (fun st => decide (fz_C_39.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_39.2.1 st.1 st.2 fz_C_39.2.2]) = fz_L_39 := by decide +kernel
theorem fz_FM_40 : (fz_S_40.filter (fun st => decide (fz_C_40.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_40.2.1 st.1 st.2 fz_C_40.2.2]) = fz_L_40 := by decide +kernel
theorem fz_FM_41 : (fz_S_41.filter (fun st => decide (fz_C_41.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_41.2.1 st.1 st.2 fz_C_41.2.2]) = fz_L_41 := by decide +kernel
theorem fz_FM_42 : (fz_S_42.filter (fun st => decide (fz_C_42.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_42.2.1 st.1 st.2 fz_C_42.2.2]) = fz_L_42 := by decide +kernel
theorem fz_FM_43 : (fz_S_43.filter (fun st => decide (fz_C_43.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_43.2.1 st.1 st.2 fz_C_43.2.2]) = fz_L_43 := by decide +kernel
theorem fz_FM_44 : (fz_S_44.filter (fun st => decide (fz_C_44.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_44.2.1 st.1 st.2 fz_C_44.2.2]) = fz_L_44 := by decide +kernel
theorem fz_FM_45 : (fz_S_45.filter (fun st => decide (fz_C_45.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_45.2.1 st.1 st.2 fz_C_45.2.2]) = fz_L_45 := by decide +kernel
theorem fz_FM_46 : (fz_S_46.filter (fun st => decide (fz_C_46.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_46.2.1 st.1 st.2 fz_C_46.2.2]) = fz_L_46 := by decide +kernel
theorem fz_FM_47 : (fz_S_47.filter (fun st => decide (fz_C_47.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_47.2.1 st.1 st.2 fz_C_47.2.2]) = fz_L_47 := by decide +kernel
theorem fz_FM_48 : (fz_S_48.filter (fun st => decide (fz_C_48.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_48.2.1 st.1 st.2 fz_C_48.2.2]) = fz_L_48 := by decide +kernel
theorem fz_FM_49 : (fz_S_49.filter (fun st => decide (fz_C_49.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_49.2.1 st.1 st.2 fz_C_49.2.2]) = fz_L_49 := by decide +kernel
theorem fz_FM_50 : (fz_S_50.filter (fun st => decide (fz_C_50.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_50.2.1 st.1 st.2 fz_C_50.2.2]) = fz_L_50 := by decide +kernel
theorem fz_FM_51 : (fz_S_51.filter (fun st => decide (fz_C_51.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_51.2.1 st.1 st.2 fz_C_51.2.2]) = fz_L_51 := by decide +kernel
theorem fz_FM_52 : (fz_S_52.filter (fun st => decide (fz_C_52.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_52.2.1 st.1 st.2 fz_C_52.2.2]) = fz_L_52 := by decide +kernel
theorem fz_FM_53 : (fz_S_53.filter (fun st => decide (fz_C_53.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_53.2.1 st.1 st.2 fz_C_53.2.2]) = fz_L_53 := by decide +kernel
theorem fz_FM_54 : (fz_S_54.filter (fun st => decide (fz_C_54.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_54.2.1 st.1 st.2 fz_C_54.2.2]) = fz_L_54 := by decide +kernel
theorem fz_FM_55 : (fz_S_55.filter (fun st => decide (fz_C_55.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_55.2.1 st.1 st.2 fz_C_55.2.2]) = fz_L_55 := by decide +kernel
theorem fz_FM_56 : (fz_S_56.filter (fun st => decide (fz_C_56.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_56.2.1 st.1 st.2 fz_C_56.2.2]) = fz_L_56 := by decide +kernel
theorem fz_FM_57 : (fz_S_57.filter (fun st => decide (fz_C_57.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_57.2.1 st.1 st.2 fz_C_57.2.2]) = fz_L_57 := by decide +kernel
theorem fz_FM_58 : (fz_S_58.filter (fun st => decide (fz_C_58.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_58.2.1 st.1 st.2 fz_C_58.2.2]) = fz_L_58 := by decide +kernel
theorem fz_FM_59 : (fz_S_59.filter (fun st => decide (fz_C_59.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_59.2.1 st.1 st.2 fz_C_59.2.2]) = fz_L_59 := by decide +kernel
theorem fz_FM_60 : (fz_S_60.filter (fun st => decide (fz_C_60.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_60.2.1 st.1 st.2 fz_C_60.2.2]) = fz_L_60 := by decide +kernel
theorem fz_FM_61 : (fz_S_61.filter (fun st => decide (fz_C_61.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_61.2.1 st.1 st.2 fz_C_61.2.2]) = fz_L_61 := by decide +kernel
theorem fz_FM_62 : (fz_S_62.filter (fun st => decide (fz_C_62.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_62.2.1 st.1 st.2 fz_C_62.2.2]) = fz_L_62 := by decide +kernel
theorem fz_FM_63 : (fz_S_63.filter (fun st => decide (fz_C_63.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_63.2.1 st.1 st.2 fz_C_63.2.2]) = fz_L_63 := by decide +kernel
theorem fz_FM_64 : (fz_S_64.filter (fun st => decide (fz_C_64.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_64.2.1 st.1 st.2 fz_C_64.2.2]) = fz_L_64 := by decide +kernel
theorem fz_FM_65 : (fz_S_65.filter (fun st => decide (fz_C_65.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_65.2.1 st.1 st.2 fz_C_65.2.2]) = fz_L_65 := by decide +kernel
theorem fz_FM_66 : (fz_S_66.filter (fun st => decide (fz_C_66.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_66.2.1 st.1 st.2 fz_C_66.2.2]) = fz_L_66 := by decide +kernel
theorem fz_FM_67 : (fz_S_67.filter (fun st => decide (fz_C_67.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_67.2.1 st.1 st.2 fz_C_67.2.2]) = fz_L_67 := by decide +kernel
theorem fz_FM_68 : (fz_S_68.filter (fun st => decide (fz_C_68.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_68.2.1 st.1 st.2 fz_C_68.2.2]) = fz_L_68 := by decide +kernel
theorem fz_FM_69 : (fz_S_69.filter (fun st => decide (fz_C_69.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_69.2.1 st.1 st.2 fz_C_69.2.2]) = fz_L_69 := by decide +kernel
theorem fz_FM_70 : (fz_S_70.filter (fun st => decide (fz_C_70.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_70.2.1 st.1 st.2 fz_C_70.2.2]) = fz_L_70 := by decide +kernel
theorem fz_FM_71 : (fz_S_71.filter (fun st => decide (fz_C_71.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_71.2.1 st.1 st.2 fz_C_71.2.2]) = fz_L_71 := by decide +kernel
theorem fz_FM_72 : (fz_S_72.filter (fun st => decide (fz_C_72.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_72.2.1 st.1 st.2 fz_C_72.2.2]) = fz_L_72 := by decide +kernel
theorem fz_FM_73 : (fz_S_73.filter (fun st => decide (fz_C_73.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_73.2.1 st.1 st.2 fz_C_73.2.2]) = fz_L_73 := by decide +kernel
theorem fz_FM_74 : (fz_S_74.filter (fun st => decide (fz_C_74.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_74.2.1 st.1 st.2 fz_C_74.2.2]) = fz_L_74 := by decide +kernel
theorem fz_FM_75 : (fz_S_75.filter (fun st => decide (fz_C_75.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_75.2.1 st.1 st.2 fz_C_75.2.2]) = fz_L_75 := by decide +kernel
theorem fz_FM_76 : (fz_S_76.filter (fun st => decide (fz_C_76.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_76.2.1 st.1 st.2 fz_C_76.2.2]) = fz_L_76 := by decide +kernel
theorem fz_FM_77 : (fz_S_77.filter (fun st => decide (fz_C_77.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_77.2.1 st.1 st.2 fz_C_77.2.2]) = fz_L_77 := by decide +kernel
theorem fz_FM_78 : (fz_S_78.filter (fun st => decide (fz_C_78.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_78.2.1 st.1 st.2 fz_C_78.2.2]) = fz_L_78 := by decide +kernel
theorem fz_FM_79 : (fz_S_79.filter (fun st => decide (fz_C_79.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_79.2.1 st.1 st.2 fz_C_79.2.2]) = fz_L_79 := by decide +kernel
theorem fz_FM_80 : (fz_S_80.filter (fun st => decide (fz_C_80.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_80.2.1 st.1 st.2 fz_C_80.2.2]) = fz_L_80 := by decide +kernel
theorem fz_FM_81 : (fz_S_81.filter (fun st => decide (fz_C_81.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_81.2.1 st.1 st.2 fz_C_81.2.2]) = fz_L_81 := by decide +kernel
theorem fz_FM_82 : (fz_S_82.filter (fun st => decide (fz_C_82.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_82.2.1 st.1 st.2 fz_C_82.2.2]) = fz_L_82 := by decide +kernel
theorem fz_FM_83 : (fz_S_83.filter (fun st => decide (fz_C_83.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_83.2.1 st.1 st.2 fz_C_83.2.2]) = fz_L_83 := by decide +kernel
theorem fz_FM_84 : (fz_S_84.filter (fun st => decide (fz_C_84.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_84.2.1 st.1 st.2 fz_C_84.2.2]) = fz_L_84 := by decide +kernel
theorem fz_FM_85 : (fz_S_85.filter (fun st => decide (fz_C_85.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_85.2.1 st.1 st.2 fz_C_85.2.2]) = fz_L_85 := by decide +kernel
theorem fz_FM_86 : (fz_S_86.filter (fun st => decide (fz_C_86.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_86.2.1 st.1 st.2 fz_C_86.2.2]) = fz_L_86 := by decide +kernel
theorem fz_FM_87 : (fz_S_87.filter (fun st => decide (fz_C_87.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_87.2.1 st.1 st.2 fz_C_87.2.2]) = fz_L_87 := by decide +kernel
theorem fz_FM_88 : (fz_S_88.filter (fun st => decide (fz_C_88.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_88.2.1 st.1 st.2 fz_C_88.2.2]) = fz_L_88 := by decide +kernel
theorem fz_FM_89 : (fz_S_89.filter (fun st => decide (fz_C_89.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_89.2.1 st.1 st.2 fz_C_89.2.2]) = fz_L_89 := by decide +kernel
theorem fz_FM_90 : (fz_S_90.filter (fun st => decide (fz_C_90.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_90.2.1 st.1 st.2 fz_C_90.2.2]) = fz_L_90 := by decide +kernel
theorem fz_FM_91 : (fz_S_91.filter (fun st => decide (fz_C_91.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_91.2.1 st.1 st.2 fz_C_91.2.2]) = fz_L_91 := by decide +kernel
theorem fz_FM_92 : (fz_S_92.filter (fun st => decide (fz_C_92.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_92.2.1 st.1 st.2 fz_C_92.2.2]) = fz_L_92 := by decide +kernel
theorem fz_FM_93 : (fz_S_93.filter (fun st => decide (fz_C_93.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_93.2.1 st.1 st.2 fz_C_93.2.2]) = fz_L_93 := by decide +kernel
theorem fz_FM_94 : (fz_S_94.filter (fun st => decide (fz_C_94.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_94.2.1 st.1 st.2 fz_C_94.2.2]) = fz_L_94 := by decide +kernel
theorem fz_FM_95 : (fz_S_95.filter (fun st => decide (fz_C_95.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_95.2.1 st.1 st.2 fz_C_95.2.2]) = fz_L_95 := by decide +kernel
theorem fz_FM_96 : (fz_S_96.filter (fun st => decide (fz_C_96.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_96.2.1 st.1 st.2 fz_C_96.2.2]) = fz_L_96 := by decide +kernel
theorem fz_FM_97 : (fz_S_97.filter (fun st => decide (fz_C_97.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_97.2.1 st.1 st.2 fz_C_97.2.2]) = fz_L_97 := by decide +kernel
theorem fz_FM_98 : (fz_S_98.filter (fun st => decide (fz_C_98.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_98.2.1 st.1 st.2 fz_C_98.2.2]) = fz_L_98 := by decide +kernel
theorem fz_FM_99 : (fz_S_99.filter (fun st => decide (fz_C_99.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_99.2.1 st.1 st.2 fz_C_99.2.2]) = fz_L_99 := by decide +kernel
theorem fz_FM_100 : (fz_S_100.filter (fun st => decide (fz_C_100.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_100.2.1 st.1 st.2 fz_C_100.2.2]) = fz_L_100 := by decide +kernel
theorem fz_FM_101 : (fz_S_101.filter (fun st => decide (fz_C_101.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_101.2.1 st.1 st.2 fz_C_101.2.2]) = fz_L_101 := by decide +kernel
theorem fz_FM_102 : (fz_S_102.filter (fun st => decide (fz_C_102.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_102.2.1 st.1 st.2 fz_C_102.2.2]) = fz_L_102 := by decide +kernel
theorem fz_FM_103 : (fz_S_103.filter (fun st => decide (fz_C_103.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_103.2.1 st.1 st.2 fz_C_103.2.2]) = fz_L_103 := by decide +kernel
theorem fz_FM_104 : (fz_S_104.filter (fun st => decide (fz_C_104.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_104.2.1 st.1 st.2 fz_C_104.2.2]) = fz_L_104 := by decide +kernel
theorem fz_FM_105 : (fz_S_105.filter (fun st => decide (fz_C_105.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_105.2.1 st.1 st.2 fz_C_105.2.2]) = fz_L_105 := by decide +kernel
theorem fz_FM_106 : (fz_S_106.filter (fun st => decide (fz_C_106.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_106.2.1 st.1 st.2 fz_C_106.2.2]) = fz_L_106 := by decide +kernel
theorem fz_FM_107 : (fz_S_107.filter (fun st => decide (fz_C_107.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_107.2.1 st.1 st.2 fz_C_107.2.2]) = fz_L_107 := by decide +kernel
theorem fz_FM_108 : (fz_S_108.filter (fun st => decide (fz_C_108.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_108.2.1 st.1 st.2 fz_C_108.2.2]) = fz_L_108 := by decide +kernel
theorem fz_FM_109 : (fz_S_109.filter (fun st => decide (fz_C_109.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_109.2.1 st.1 st.2 fz_C_109.2.2]) = fz_L_109 := by decide +kernel
theorem fz_FM_110 : (fz_S_110.filter (fun st => decide (fz_C_110.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_110.2.1 st.1 st.2 fz_C_110.2.2]) = fz_L_110 := by decide +kernel
theorem fz_FM_111 : (fz_S_111.filter (fun st => decide (fz_C_111.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_111.2.1 st.1 st.2 fz_C_111.2.2]) = fz_L_111 := by decide +kernel
theorem fz_FM_112 : (fz_S_112.filter (fun st => decide (fz_C_112.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_112.2.1 st.1 st.2 fz_C_112.2.2]) = fz_L_112 := by decide +kernel
theorem fz_FM_113 : (fz_S_113.filter (fun st => decide (fz_C_113.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_113.2.1 st.1 st.2 fz_C_113.2.2]) = fz_L_113 := by decide +kernel
theorem fz_FM_114 : (fz_S_114.filter (fun st => decide (fz_C_114.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_114.2.1 st.1 st.2 fz_C_114.2.2]) = fz_L_114 := by decide +kernel
theorem fz_FM_115 : (fz_S_115.filter (fun st => decide (fz_C_115.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_115.2.1 st.1 st.2 fz_C_115.2.2]) = fz_L_115 := by decide +kernel
theorem fz_FM_116 : (fz_S_116.filter (fun st => decide (fz_C_116.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_116.2.1 st.1 st.2 fz_C_116.2.2]) = fz_L_116 := by decide +kernel
theorem fz_FM_117 : (fz_S_117.filter (fun st => decide (fz_C_117.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_117.2.1 st.1 st.2 fz_C_117.2.2]) = fz_L_117 := by decide +kernel
theorem fz_FM_118 : (fz_S_118.filter (fun st => decide (fz_C_118.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_118.2.1 st.1 st.2 fz_C_118.2.2]) = fz_L_118 := by decide +kernel
theorem fz_FM_119 : (fz_S_119.filter (fun st => decide (fz_C_119.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_119.2.1 st.1 st.2 fz_C_119.2.2]) = fz_L_119 := by decide +kernel
theorem fz_FM_120 : (fz_S_120.filter (fun st => decide (fz_C_120.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_120.2.1 st.1 st.2 fz_C_120.2.2]) = fz_L_120 := by decide +kernel
theorem fz_FM_121 : (fz_S_121.filter (fun st => decide (fz_C_121.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_121.2.1 st.1 st.2 fz_C_121.2.2]) = fz_L_121 := by decide +kernel
theorem fz_FM_122 : (fz_S_122.filter (fun st => decide (fz_C_122.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_122.2.1 st.1 st.2 fz_C_122.2.2]) = fz_L_122 := by decide +kernel
theorem fz_FM_123 : (fz_S_123.filter (fun st => decide (fz_C_123.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_123.2.1 st.1 st.2 fz_C_123.2.2]) = fz_L_123 := by decide +kernel
theorem fz_FM_124 : (fz_S_124.filter (fun st => decide (fz_C_124.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_124.2.1 st.1 st.2 fz_C_124.2.2]) = fz_L_124 := by decide +kernel
theorem fz_FM_125 : (fz_S_125.filter (fun st => decide (fz_C_125.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_125.2.1 st.1 st.2 fz_C_125.2.2]) = fz_L_125 := by decide +kernel
theorem fz_FM_126 : (fz_S_126.filter (fun st => decide (fz_C_126.2.1 ≤ st.1))).flatMap
    (fun st => [st, step1 fz_C_126.2.1 st.1 st.2 fz_C_126.2.2]) = fz_L_126 := by decide +kernel
