# Logo Classifier using GoogLeNet

This project trains a logo classifier using a pre-trained GoogLeNet model fine-tuned on a custom dataset of logos. The dataset consists of images from ten different brands, and the model classifies an input image into one of these ten classes and an unknown class.

## Dependencies

To run the code, you will need the following libraries:

- PyTorch
- torchvision
- NumPy
- scikit-learn
- Pillow
- Matplotlib

You can install them using pip:

```sh
pip install torch torchvision numpy scikit-learn pillow matplotlib
```

## Dataset

The dataset contains images of logos from the following brands:

1. Nike
2. Adidas
3. Ford
4. Honda
5. General Mills
6. Unilever
7. McDonald's
8. KFC
9. Gators
10. 3M

The images are stored in a NumPy array (`data_train.npy`), and the corresponding labels are stored in a separate NumPy array (`labels_train.npy`).

There is also a dataset `data_unknown.npy` containing a diverse set of images used for training the unknown class, and `labels_unknown.npy` containing the labels (-1) for this class.

## Files

`train.ipynb`: Jupyter notebook for training the logo classifier.

`test.ipynb`: Jupyter notebook for evaluating the trained model on the test dataset.

`googlenet_with_unknown.pth`: The state dictionary of the trained model.

`experiments`: A folder containing other experiments on models including GoogLeNet without data augmentation, SVM, ResNet51 and DenseNet121.

## Usage

1. Run the train_logo_classifier.ipynb notebook to train the logo classifier. The notebook loads the training data, pre-processes the images, and trains a GoogLeNet model with the following steps:

    1. Load the dataset:

    ```python
    data_train = np.load('data_train.npy')
    labels_train = np.load('labels_train.npy')
    ```
    
    Notice that the `data_train` here is $D\times N$, and `labels_train` is $N\times 1$, where $D$ is the dimension of the images, and $N$ is the number of samples. `data_unknown.npy` and `labels_unknown.npy` should be loaded in the same way.

    2. Perform integer encoding for the labels and create the custom dataset using the `LogoDataset` class.

    3. Split the dataset into a training set and a validation set, and create data loaders for them.

    4. Implement data augmentation for the training dataset.

    5. Set up the pre-trained GoogLeNet model, and update the last layer to match the number of logo classes.

    6. Train the model using early stopping to prevent overfitting.

    7. Save the trained model as `googlenet.pth`.

    8. Visualize the training and validation losses and accuracies.


2. Run the `test.ipynb` notebook to evaluate the trained model on the test dataset. The notebook performs the following steps:

    1. Load the test dataset:

    ```python
    test_data = np.load('data_test.npy')
    test_labels = np.load('labels_test.npy')
    ```
    
    Again, the `data_test` here is $D\times N$, and `labels_test` is $N\times 1$, where $D$ is the dimension of the images, and $N$ is the number of samples.

    2. Define the image transformations to be applied on the test dataset, which is the same with the validation set transformation in `train.ipynb`.

    3. Create the custom dataset using the `LogoDataset` class.

    5. Load the saved GoogLeNet model.

    6. Evaluate the model on the test dataset.

    7. Print the accuracy of the model on the test dataset along with the predicted labels.

## Results

The trained model achieves high accuracy on both the training and validation sets. The training is stopped early when the validation loss does not improve for three consecutive epochs to prevent overfitting. The training and validation loss and accuracy plots help visualize the performance of the model during training.

## Authors

Jiamin Chen - jiamin.chen@ufl.edu


Kai Wei - kai.wei@ufl.edu


Nikodem Gazda - ngazda@ufl.edu

Project Link: https://github.com/UF-FundMachineLearning-Sp23/final-project-supergator/

## Acknowledgements

[Catia Silva](https://faculty.eng.ufl.edu/catia-silva/)

## Thank you
