package main

import (
	"encoding/csv"
	"fmt"
	"math"
	"os"
	"sort"
	"strconv"
	"sync"
	"time"
)

type Trip struct {
	PassengerCount      float64
	TripDistance        float64
	FareAmount          float64
	PaymentType         float64
	CongestionSurcharge float64
	TipLabel            int
}

// ---------- Funciones de ML ----------

func sigmoid(z float64) float64 {
	return 1.0 / (1.0 + math.Exp(-z))
}

func predict(trip Trip, weights []float64) float64 {
	z := weights[0]*trip.PassengerCount +
		weights[1]*trip.TripDistance +
		weights[2]*trip.FareAmount +
		weights[3]*trip.PaymentType +
		weights[4]*trip.CongestionSurcharge
	return sigmoid(z)
}

func trainBatch(trips []Trip, weights []float64, lr float64, wg *sync.WaitGroup, mu *sync.Mutex) {
	defer wg.Done()
	grad := make([]float64, len(weights))

	for _, trip := range trips {
		pred := predict(trip, weights)
		error := float64(trip.TipLabel) - pred
		grad[0] += error * trip.PassengerCount
		grad[1] += error * trip.TripDistance
		grad[2] += error * trip.FareAmount
		grad[3] += error * trip.PaymentType
		grad[4] += error * trip.CongestionSurcharge
	}

	mu.Lock()
	for i := range weights {
		weights[i] += lr * grad[i]
	}
	mu.Unlock()
}

func runTraining(trips []Trip) time.Duration {
	start := time.Now()

	weights := []float64{0.1, 0.1, 0.1, 0.1, 0.1}
	lr := 0.0001
	batchSize := 50000
	numBatches := len(trips) / batchSize

	var wg sync.WaitGroup
	var mu sync.Mutex

	for epoch := 0; epoch < 1; epoch++ {
		for i := 0; i < numBatches; i++ {
			start := i * batchSize
			end := start + batchSize
			if end > len(trips) {
				end = len(trips)
			}
			wg.Add(1)
			go trainBatch(trips[start:end], weights, lr, &wg, &mu)
		}
		wg.Wait()
	}

	return time.Since(start)
}

// ---------- Cargar CSV ----------

func loadTrips(filename string) []Trip {
	file, err := os.Open(filename)
	if err != nil {
		panic(err)
	}
	defer file.Close()

	reader := csv.NewReader(file)
	records, err := reader.ReadAll()
	if err != nil {
		panic(err)
	}

	var trips []Trip
	for i, line := range records {
		if i == 0 {
			continue
		}
		passengerCount, _ := strconv.ParseFloat(line[3], 64)
		tripDistance, _ := strconv.ParseFloat(line[4], 64)
		paymentType, _ := strconv.ParseFloat(line[9], 64)
		fareAmount, _ := strconv.ParseFloat(line[10], 64)
		congestionSurcharge, _ := strconv.ParseFloat(line[17], 64)
		tipAmount, _ := strconv.ParseFloat(line[13], 64)

		label := 0
		if tipAmount > 3.0 {
			label = 1
		}

		trips = append(trips, Trip{
			PassengerCount:      passengerCount,
			TripDistance:        tripDistance,
			FareAmount:          fareAmount,
			PaymentType:         paymentType,
			CongestionSurcharge: congestionSurcharge,
			TipLabel:            label,
		})
	}
	return trips
}

// ---------- Menú principal ----------

func showMenu() {
	fmt.Println("=== PredictTipApp ===")
	fmt.Println("1. Entrenar modelo concurrente")
	fmt.Println("2. Ejecutar pruebas (1000 veces + media recortada)")
	fmt.Println("3. Salir")
	fmt.Print("Ingrese una opción: ")
}

func main() {
	trips := loadTrips("yellow_tripdata_2021-01.csv")
	fmt.Printf("Datos cargados: %d registros\n\n", len(trips))

	var option int
	for {
		showMenu()
		fmt.Scan(&option)

		switch option {
		case 1:
			start := time.Now()
			runTraining(trips)
			fmt.Printf("Entrenamiento completo en %.3f segundos\n\n", time.Since(start).Seconds())
		case 2:
			fmt.Println("Ejecutando 1000 pruebas...")
			var times []float64
			for i := 0; i < 1000; i++ {
				dur := runTraining(trips)
				times = append(times, dur.Seconds())
				if i%100 == 0 {
					fmt.Printf("  %d ejecuciones completadas\n", i)
				}
			}
			sort.Float64s(times)
			times = times[50 : len(times)-50] // media recortada
			var sum float64
			for _, t := range times {
				sum += t
			}
			avg := sum / float64(len(times))
			fmt.Printf("Tiempo promedio (media recortada): %.6f segundos\n\n", avg)
		case 3:
			fmt.Println("Saliendo de la aplicación.")
			return
		default:
			fmt.Println("Opción no válida.")
		}
	}
}